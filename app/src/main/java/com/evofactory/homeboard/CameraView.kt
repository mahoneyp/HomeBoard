package com.evofactory.homeboard

import android.content.Context
import android.content.pm.ApplicationInfo
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.net.ConnectivityManager
import android.net.Network
import android.net.Uri
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.view.Gravity
import android.view.PixelCopy
import android.view.SurfaceView
import android.view.ViewGroup
import android.widget.FrameLayout
import androidx.annotation.OptIn
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.Image
import androidx.compose.foundation.background
import androidx.compose.foundation.focusable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.aspectRatio
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.runtime.Composable
import androidx.compose.runtime.SideEffect
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableIntStateOf
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.produceState
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.focus.FocusRequester
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.geometry.toRect
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.Path
import androidx.compose.ui.graphics.PathFillType
import androidx.compose.ui.graphics.addOutline
import androidx.compose.ui.graphics.asImageBitmap
import androidx.compose.ui.input.key.Key
import androidx.compose.ui.input.key.KeyEventType
import androidx.compose.ui.input.key.key
import androidx.compose.ui.input.key.onPreviewKeyEvent
import androidx.compose.ui.input.key.type
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.text.style.TextOverflow
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.dp
import androidx.compose.ui.viewinterop.AndroidView
import androidx.compose.ui.window.Dialog
import androidx.compose.ui.window.DialogProperties
import androidx.lifecycle.compose.LifecycleStartEffect
import androidx.media3.common.AudioAttributes
import androidx.media3.common.C
import androidx.media3.common.Format
import androidx.media3.common.MediaItem
import androidx.media3.common.MimeTypes
import androidx.media3.common.PlaybackException
import androidx.media3.common.Player
import androidx.media3.common.Tracks
import androidx.media3.common.VideoSize
import androidx.media3.common.util.UnstableApi
import androidx.media3.exoplayer.DefaultLoadControl
import androidx.media3.exoplayer.ExoPlayer
import androidx.media3.exoplayer.mediacodec.MediaCodecAdapter
import androidx.media3.exoplayer.DefaultRenderersFactory
import androidx.media3.exoplayer.rtsp.RtspMediaSource
import androidx.media3.ui.AspectRatioFrameLayout
import androidx.tv.material3.MaterialTheme
import androidx.tv.material3.Text
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.delay
import kotlinx.coroutines.withContext
import java.io.File
import java.io.InputStream
import java.net.ConnectException
import java.net.Inet4Address
import java.net.InetAddress
import java.net.InetSocketAddress
import java.net.NoRouteToHostException
import java.net.Socket
import java.net.SocketTimeoutException
import java.net.UnknownHostException
import java.time.Instant
import java.time.LocalDate
import java.time.ZoneId
import java.time.format.DateTimeFormatter
import java.util.concurrent.Executors
import javax.net.SocketFactory
import kotlin.concurrent.thread
import kotlin.math.abs

// Logcat tag for connection events (losses, retries, recoveries); never logs the address
private const val TAG = "CameraView"

// How often the TV's address is checked while it has none yet (e.g. just after standby)
private const val NETWORK_CHECK_INTERVAL_MS = 500L

// Connecting to the camera is also the check that it can be reached. On a home network it answers
// within milliseconds; 2 s leaves room for slow, older cameras. Without a limit the system waits
// minutes, and the player can't be stopped meanwhile.
private const val SOCKET_CONNECT_TIMEOUT_MS = 2_000

// Camera unreachable: attempts start at most this often, so a timeout is retried at once but an
// instant refusal (camera rebooting) doesn't turn into a flood
private const val UNREACHABLE_RETRY_INTERVAL_MS = 1_000L

// The camera answered but streaming failed (wrong login, no stream…): retrying sooner wouldn't help
private const val RETRY_DELAY_MS = 3_000L

// The camera's description of its stream won't change by itself: no point asking often
private const val DESCRIPTION_RETRY_DELAY_MS = 30_000L

// Picture stuck this long = camera gone, even without an error
private const val FROZEN_TIMEOUT_MS = 5_000L

// "Playing" but the picture is still all black this long = no real picture. Leaves room for a camera's
// first full frame, which can take a few seconds after joining the stream
private const val BLACK_PICTURE_TIMEOUT_MS = 8_000L
private const val BLACK_PICTURE_CHECK_INTERVAL_MS = 1_000L

// Longer while connecting: UDP waits 8 s for packets before switching to TCP
private const val CONNECT_TIMEOUT_MS = 12_000L

// Buffer only a few hundred ms: enough to start, little added delay
private const val MIN_BUFFER_MS = 500
private const val MAX_BUFFER_MS = 2_000
private const val START_BUFFER_MS = 100

// If playback falls behind live (e.g. after a stall on TCP), speed up until caught up
private const val BEHIND_LIMIT_MS = 800
private const val CAUGHT_UP_MS = 200
private const val CATCH_UP_SPEED = 1.5f

// Width of the saved last picture; it's only shown dimmed behind the status
private const val SNAPSHOT_WIDTH = 960

// Copies of the live picture are taken this often: once the launcher is closing, the window is
// already hidden and there's nothing left to copy
private const val SNAPSHOT_INTERVAL_MS = 10_000L

// Several play at once in the grid: copy their pictures less often
private const val COMPACT_SNAPSHOT_INTERVAL_MS = 60_000L

// A camera only glanced at still gets a picture: one soon after it's live, replaced once the picture has settled
private const val FIRST_SNAPSHOT_DELAY_MS = 500L
private const val SETTLED_SNAPSHOT_DELAY_MS = 4_000L

// Also to disk now and then, so a restart that skips the release doesn't lose the picture
private const val SNAPSHOT_SAVE_INTERVAL_MS = 300_000L

// Same corners as the app tiles (TV Material's default card shape)
val CameraShape = RoundedCornerShape(8.dp)

/** A stretched camera picture's shape: the TV's */
const val STRETCHED_ASPECT = 16f / 9f

// Error line of the status: readable on the dark chip, clearly not the normal text
val ErrorColor = Color(0xFFFFB4AB)

private enum class Phase {
    /** Streaming attempt in progress, waiting for the first picture */
    Connecting,
    Live,

    /** The TV has no usable IPv4 address yet, e.g. just after standby */
    WaitingForNetwork,

    /** Waiting before the next attempt */
    RetryScheduled,
}

/** Where the stream stands, for the status shown while there's no live picture */
private class ConnectionStatus(val cameraHost: String) {
    var phase by mutableStateOf(Phase.Connecting)

    /** When the picture was lost, or when connecting began if it never came; null while first connecting */
    var lostAt by mutableStateOf<Long?>(null)

    /** Streaming attempts since the picture was lost (or since the first one failed) */
    var retries by mutableIntStateOf(0)

    /** When the next streaming attempt starts (elapsedRealtime), in RetryScheduled */
    var nextRetryAt by mutableStateOf(0L)

    /** What's missing, in WaitingForNetwork */
    var networkProblem by mutableStateOf("")

    /** In Connecting: the camera answered, with its video format if known (e.g. "H.265 2560×1440") */
    var cameraAnswered by mutableStateOf<String?>(null)

    var lastError by mutableStateOf<String?>(null)

    /** Before connecting: other players are still releasing their decoders */
    var waitingForDecoders by mutableStateOf(false)

    val live get() = phase == Phase.Live

    /** Something went wrong, rather than only still connecting */
    val failing get() = lastError != null || phase == Phase.WaitingForNetwork

    fun reset(phase: Phase) {
        this.phase = phase
        lostAt = null
        retries = 0
        cameraAnswered = null
        lastError = null
    }

    /** Marks the start of an outage, unless already in one */
    fun lost(at: Long = System.currentTimeMillis()) {
        if (lostAt == null) lostAt = at
    }
}

private val NotLiveColor = Color(0xFFE53935)

/** The red X in the bottom right corner of a picture that isn't live */
@Composable
fun NotLiveMark(modifier: Modifier = Modifier, size: Dp = 24.dp) {
    MdiIcon("mdi:close-thick", modifier = modifier, size = size, color = NotLiveColor)
}

/**
 * Live RTSP camera, muted. Streams only while the launcher is visible, reconnects on its own. While
 * there's no live picture, shows the last one dimmed, with when it was lost and the retries.
 * The codec isn't restricted: H.264 or H.265 play if the TV can decode them.
 *
 * [compact] is for small views: shorter status. [fallbackPictureUrl]: whose last picture to show when
 * this stream has none of its own, e.g. the main stream of the camera this is a substream of.
 * Not live, it shows a [NotLiveMark], or if [compact] leaves that to its owner through [onLiveChange].
 *
 * [fullScreen] moves the picture to a window over everything, with the same player and stream; OK
 * or Back calls [onCloseFullScreen], and a number button calls [onCameraButton] with the camera's
 * 0-based index. With [waitForOtherPlayers], it only connects once every other player has released,
 * for TVs that refuse a decoder until then; with [minimizeStreams], once those already stopping have.
 *
 * [useAudio] off takes the stream's audio tracks out of the camera's description, so the player never
 * sees them. Otherwise its sound plays in full screen. With [fullScreenSound], the audio plays muted
 * until then: a player can't add audio to a stream that's playing, the camera refuses it.
 *
 * [stretch] shows the picture, and its saved copy, at 16:9 whatever the stream's shape, e.g. for a
 * 4:3 substream of a 16:9 camera.
 *
 * [showProgress] off leaves out the status while it's only connecting: it shows once something fails.
 */
@Composable
fun CameraView(
    url: String,
    useTcp: Boolean,
    modifier: Modifier = Modifier,
    compact: Boolean = false,
    fallbackPictureUrl: String? = null,
    minimizeStreams: Boolean = false,
    useAudio: Boolean = true,
    fullScreenSound: Boolean = false,
    fullScreen: Boolean = false,
    onCloseFullScreen: () -> Unit = {},
    onCameraButton: (Int) -> Unit = {},
    // Full screen: the remote's channel up (1) or down (-1)
    onChannel: (Int) -> Unit = {},
    waitForOtherPlayers: Boolean = false,
    onLiveChange: (Boolean) -> Unit = {},
    showProgress: Boolean = true,
    // Off when the picture fills the screen
    rounded: Boolean = true,
    stretch: Boolean = false,
) {
    val context = LocalContext.current
    val status = remember(url) { ConnectionStatus(Uri.parse(url).host.orEmpty()) }
    LaunchedEffect(status.live) { onLiveChange(status.live) }
    val snapshots = remember(url) { SnapshotStore(context.filesDir, url) }

    // A SurfaceView: decoded frames go straight to the TV's hardware video layer, the cheapest and
    // fastest path (a TextureView would copy each frame through the GPU)
    val frame = remember { AspectRatioFrameLayout(context).apply { resizeMode = AspectRatioFrameLayout.RESIZE_MODE_FIT } }
    val video = remember {
        SurfaceView(context).also {
            // Centred: the frame itself is laid out over the whole space, only the picture takes the stream's shape
            frame.addView(it, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT, Gravity.CENTER))
            // The picture's layer only follows the view when the window draws again, and Compose may lay the view
            // out after this frame's drawing started: on a still screen, like full screen, the layer kept the last
            // camera's size and place, squeezing the picture and showing the launcher around it (Kitchen TV, 2026-11-05)
            it.addOnLayoutChangeListener { view, left, top, right, bottom, oldLeft, oldTop, oldRight, oldBottom ->
                if (left != oldLeft || top != oldTop || right != oldRight || bottom != oldBottom) view.postOnAnimation { frame.invalidate() }
            }
        }
    }

    val shape = CameraShape
    val background = MaterialTheme.colorScheme.surface

    LaunchedEffect(snapshots) { snapshots.load() }

    var mayConnect by remember(url) { mutableStateOf(!waitForOtherPlayers && !minimizeStreams) }
    val withAudio = useAudio && (fullScreenSound || fullScreen)
    // Heard in full screen only
    val audible = withAudio && fullScreen
    val current = remember { mutableStateOf<CameraConnection?>(null) }
    if (mayConnect) {
        LifecycleStartEffect(url, useTcp, useAudio, withAudio, minimizeStreams) {
            val snapshotInterval = if (compact) COMPACT_SNAPSHOT_INTERVAL_MS else SNAPSHOT_INTERVAL_MS
            val connection = CameraConnection(
                context, url, useTcp, useAudio, withAudio, audible, stretch, video, frame, status, snapshots, snapshotInterval, minimizeStreams,
            )
            current.value = connection
            onStopOrDispose {
                connection.release()
                current.value = null
            }
        }
        // Without restarting the stream
        SideEffect {
            current.value?.audible = audible
            current.value?.stretch = stretch
        }
    } else {
        LaunchedEffect(url) {
            val label = "Player ${Integer.toHexString(url.hashCode()).takeLast(4)}"
            awaitPlayersGone(label, releasedOnly = !waitForOtherPlayers) { status.waitingForDecoders = true }
            status.waitingForDecoders = false
            mayConnect = true
        }
    }

    // Here or full screen: the player draws into the same view, which moves between the two
    @Composable
    fun Picture(modifier: Modifier, rounded: Boolean) = Box(
        modifier = (if (rounded) modifier.clip(shape) else modifier).background(Color.Black),
        contentAlignment = Alignment.Center,
    ) {
        AndroidView(
            factory = {
                // Still in the other place's view, which may not be gone yet
                (frame.parent as? ViewGroup)?.removeView(frame)
                frame.apply {
                    // Display only: the remote should never land on it
                    isFocusable = false
                    descendantFocusability = ViewGroup.FOCUS_BLOCK_DESCENDANTS
                }
            },
            modifier = Modifier.fillMaxSize(),
        )
        val fallbackPicture = fallbackPictureUrl?.let { cameraSnapshot(it) }
        val snapshot = snapshots.snapshot ?: fallbackPicture
        if (!status.live) {
            // Opaque, over whatever old frame the video layer still holds (maybe from another camera)
            Box(Modifier.fillMaxSize().background(Color.Black)) {
                if (snapshot != null) {
                    Image(
                        snapshot.image,
                        contentDescription = null,
                        contentScale = if (stretch) ContentScale.FillBounds else ContentScale.Fit,
                        modifier = if (stretch) Modifier.align(Alignment.Center).aspectRatio(STRETCHED_ASPECT) else Modifier.fillMaxSize(),
                    )
                }
            }
            // Dimmed: clearly not live
            Box(Modifier.fillMaxSize().background(Color.Black.copy(alpha = 0.6f)))
            if (compact) {
                CompactCameraStatus(status)
            } else {
                if (showProgress || status.failing) CameraStatus(status, snapshot?.takenAt)
                NotLiveMark(Modifier.align(Alignment.BottomEnd).padding(16.dp), size = 36.dp)
            }
        }
        // The hardware video layer ignores clipping: its corners are painted over in the background colour
        if (rounded) {
            Canvas(Modifier.matchParentSize()) {
                val corners = Path().apply {
                    fillType = PathFillType.EvenOdd
                    addRect(size.toRect())
                    addOutline(shape.createOutline(size, layoutDirection, this@Canvas))
                }
                drawPath(corners, background)
            }
        }
    }

    if (fullScreen) {
        FullScreenWindow(onClose = onCloseFullScreen, onCameraButton = onCameraButton, onChannel = onChannel) { Picture(Modifier.fillMaxSize(), rounded = false) }
    } else {
        Picture(modifier, rounded = rounded)
    }
}

/**
 * Over everything, on black. OK or Back closes it, on release, so it can't be the press that opened it.
 * A window of its own, so it handles the number buttons itself.
 */
@Composable
private fun FullScreenWindow(onClose: () -> Unit, onCameraButton: (Int) -> Unit, onChannel: (Int) -> Unit, content: @Composable () -> Unit) {
    val focus = remember { FocusRequester() }
    Dialog(onDismissRequest = onClose, properties = DialogProperties(usePlatformDefaultWidth = false)) {
        LaunchedEffect(Unit) { focus.requestFocus() }
        Box(
            modifier = Modifier
                .fillMaxSize()
                .background(Color.Black)
                .focusRequester(focus)
                .onPreviewKeyEvent { event ->
                    cameraButtonIndex(event)?.let { index ->
                        if (event.type == KeyEventType.KeyDown) onCameraButton(index)
                        return@onPreviewKeyEvent true
                    }
                    channelStep(event)?.let { step ->
                        if (event.type == KeyEventType.KeyDown) onChannel(step)
                        return@onPreviewKeyEvent true
                    }
                    when (event.key) {
                        Key.DirectionCenter, Key.Enter, Key.NumPadEnter, Key.Escape -> {
                            if (event.type == KeyEventType.KeyUp) onClose()
                            true
                        }
                        else -> false
                    }
                }
                .focusable(),
        ) { content() }
    }
}

private var openPlayers = 0
private const val MAX_QUIET_RETRIES = 15
private const val QUIET_RETRY_DELAY_MS = 200L

/**
 * Some older TVs refuse a decoder asked for while another is opening. Only opening them takes turns,
 * which is quick: cameras still connect at the same time.
 */
@OptIn(UnstableApi::class)
private class OneAtATimeRenderers(context: Context) : DefaultRenderersFactory(context) {
    override fun getCodecAdapterFactory(): MediaCodecAdapter.Factory {
        val factory = super.getCodecAdapterFactory()
        return MediaCodecAdapter.Factory { configuration ->
            synchronized(decoderOpening) { factory.createAdapter(configuration) }
        }
    }
}

private val decoderOpening = Any()

private const val STUCK_PLAYER_MESSAGE = "A stuck video player is holding a decoder: restart the app from the warning in the top bar"

/**
 * Owns the player for one visit of the launcher. Waits until the TV has a usable address, then
 * streams, watches the picture, and starts over when it's lost.
 */
@OptIn(UnstableApi::class)
private class CameraConnection(
    private val context: Context,
    private val url: String,
    private val useTcp: Boolean,
    // Off, its audio tracks are taken out of the camera's description, so the player never sees them
    private val useAudio: Boolean,
    // Plays the audio track, muted unless [audible]
    private val withAudio: Boolean,
    audible: Boolean,
    stretch: Boolean,
    private val video: SurfaceView,
    private val frame: AspectRatioFrameLayout,
    private val status: ConnectionStatus,
    private val snapshots: SnapshotStore,
    private val snapshotInterval: Long,
    private val decodersTakeTurns: Boolean,
) {
    private val handler = Handler(Looper.getMainLooper())
    private val connectivity = context.getSystemService(ConnectivityManager::class.java)
    private var waitingForNetworkSince = 0L
    private var attemptStartedAt = 0L
    private var lastFrames = 0
    private var lastProgressAt = 0L
    private var liveAt = 0L
    private var pictureSeen = false
    private var lastPictureCheckAt = 0L
    private var nextSnapshotAt = 0L
    private var settledCopyDone = false
    private var lastSavedAt = 0L
    private var lastNetwork = connectivity.activeNetwork
    private var needsNewPlayer = false
    private var replacingPlayer = false

    // What the camera last described, from the player's thread
    @Volatile
    private var tracks: List<SdpTrack>? = null

    // The camera describes audio but sends none: the player would wait for it forever
    private var silentAudio = false

    /** Sound on, e.g. in full screen. Changes on the same stream, without starting over. */
    var audible = audible
        set(value) {
            if (field == value) return
            field = value
            player.applyAudio()
        }

    // The picture's shape as the stream sends it, 0 until known
    private var videoAspect = 0f

    /** 16:9 whatever the stream's shape. Changes on the same stream, without starting over. */
    var stretch = stretch
        set(value) {
            if (field == value) return
            field = value
            applyAspect()
        }

    private fun applyAspect() = frame.setAspectRatio(if (stretch) STRETCHED_ASPECT else videoAspect)

    private var player = createPlayer()

    private fun createPlayer() = ExoPlayer.Builder(context, if (decodersTakeTurns) OneAtATimeRenderers(context) else DefaultRenderersFactory(context))
        .setLoadControl(
            DefaultLoadControl.Builder()
                .setBufferDurationsMs(MIN_BUFFER_MS, MAX_BUFFER_MS, START_BUFFER_MS, START_BUFFER_MS)
                .build(),
        )
        .build()
        .apply {
            applyAudio()
            setMediaSource(
                RtspMediaSource.Factory()
                    .setForceUseRtpTcp(useTcp)
                    .setSocketFactory(CameraSocketFactory(::onDescription))
                    // Debug builds log the RTSP exchange with the camera (logcat tag RtspClient)
                    .setDebugLoggingEnabled(context.applicationInfo.flags and ApplicationInfo.FLAG_DEBUGGABLE != 0)
                    .createMediaSource(MediaItem.fromUri(url)),
            )
            setVideoSurfaceView(video)
            addListener(object : Player.Listener {
                override fun onRenderedFirstFrame() = onLive()

                override fun onPlayerError(error: PlaybackException) = onStreamError(error)

                // The camera described its stream and accepted the login: only the picture is missing
                override fun onTracksChanged(tracks: Tracks) {
                    if (status.phase != Phase.Connecting || tracks.isEmpty) return
                    val format = tracks.groups.firstOrNull { it.type == C.TRACK_TYPE_VIDEO }?.getTrackFormat(0)
                    status.cameraAnswered = format?.let { describeVideo(it) } ?: ""
                }

                override fun onVideoSizeChanged(videoSize: VideoSize) {
                    if (videoSize.height > 0) {
                        videoAspect = videoSize.width * videoSize.pixelWidthHeightRatio / videoSize.height
                        applyAspect()
                    }
                }
            })
            playWhenReady = true
        }

    // Without the audio track, video plays on its own clock, without waiting for it
    private fun ExoPlayer.applyAudio() {
        val playing = withAudio && !silentAudio
        trackSelectionParameters = trackSelectionParameters.buildUpon()
            .setTrackTypeDisabled(C.TRACK_TYPE_AUDIO, !playing)
            .build()
        volume = if (audible) 1f else 0f
        // Other apps' sound pauses only while this one is heard
        setAudioAttributes(CAMERA_AUDIO, playing && audible)
    }

    // On the player's thread: logs what the camera describes, and takes out its audio if unused
    private fun onDescription(sdp: String): String {
        val fixedSdp = sdp.replace(Regex("(?m)^s=[ \\t]*(?=\\r?$)"), "s=-")
        val described = sdpTracks(fixedSdp)
        val takeOut = !useAudio && described.any { it.media == "audio" }
        if (described != tracks) {
            AppLog.i(TAG, "Player $logId tracks: ${described.joinToString()}" + if (takeOut) ", audio taken out" else "")
        }
        tracks = described
        return if (takeOut) sdpWithoutAudio(fixedSdp) else fixedSdp
    }

    private val attempt = Runnable { attempt() }

    private val tick = object : Runnable {
        override fun run() {
            check()
            handler.postDelayed(this, 500)
        }
    }

    private val logId = Integer.toHexString(url.hashCode()).takeLast(4)
    private var quietRetries = 0
    private var released = false
    private var playerWatch = PlayerWatch(player, "Player $logId")

    // Sockets on the old network are dead, even if the player hasn't noticed yet
    private val networkCallback = object : ConnectivityManager.NetworkCallback() {
        override fun onAvailable(network: Network) {
            if (network == lastNetwork) return
            AppLog.i(TAG, "Player $logId: the network changed")
            when (status.phase) {
                Phase.Live, Phase.Connecting -> lose("The TV's network changed", unreachable = true)
                Phase.RetryScheduled -> attempt()
                else -> Unit
            }
        }
    }

    init {
        openPlayers += 1
        AppLog.i(TAG, "Player $logId started over ${if (useTcp) "TCP" else "UDP"}, open: $openPlayers")
        status.reset(Phase.Connecting)
        // Known before the stream's own shape is
        if (stretch) applyAspect()
        attempt()
        handler.post(tick)
        connectivity.registerDefaultNetworkCallback(networkCallback, handler)
    }

    fun release() {
        connectivity.unregisterNetworkCallback(networkCallback)
        // Kept for next time: shown dimmed while reconnecting, e.g. when the TV comes back on
        if (status.live) snapshots.save()
        snapshots.logCopies()
        // Already dimmed when the launcher shows again, instead of the video layer's old frame
        status.phase = Phase.Connecting
        handler.removeCallbacksAndMessages(null)
        released = true
        playerWatch.release()
        openPlayers -= 1
        AppLog.i(TAG, "Player $logId released, open: $openPlayers")
    }

    /** Connects to the camera once the TV has a usable address; until then checks again every 500 ms */
    private fun attempt() {
        handler.removeCallbacks(attempt)
        val now = SystemClock.elapsedRealtime()
        val (address, problem) = tvAddress()
        if (address == null) {
            if (status.phase != Phase.WaitingForNetwork || status.networkProblem != problem) {
                AppLog.i(TAG, "Network down: $problem")
                if (status.phase != Phase.WaitingForNetwork) waitingForNetworkSince = now
                status.networkProblem = problem
                status.phase = Phase.WaitingForNetwork
            }
            handler.postDelayed(attempt, NETWORK_CHECK_INTERVAL_MS)
            return
        }
        if (status.phase == Phase.WaitingForNetwork) {
            AppLog.i(TAG, "TV address ${address.hostAddress} after ${now - waitingForNetworkSince} ms")
        }
        if (status.lostAt != null) {
            status.retries += 1
            AppLog.i(TAG, "Player $logId retry ${status.retries}")
        }
        status.cameraAnswered = null
        status.phase = Phase.Connecting
        attemptStartedAt = now
        val network = connectivity.activeNetwork
        if (needsNewPlayer || network != lastNetwork) replacePlayer()
        lastNetwork = network
        player.stop()
        player.prepare()
    }

    /**
     * After the network comes back, a player that was already open can go on getting no picture for
     * about 2 minutes, while a new one gets it right away.
     */
    private fun replacePlayer() {
        needsNewPlayer = false
        AppLog.i(TAG, "Player $logId: starting over with a new player")
        replacingPlayer = true
        playerWatch.release()
        replacingPlayer = false
        player = createPlayer()
        playerWatch = PlayerWatch(player, "Player $logId")
    }

    /**
     * The TV's IPv4 address on its current network, or why there's none. A self-assigned address
     * (169.254.x.x) doesn't count: the TV makes one up when DHCP hasn't answered (yet).
     */
    private fun tvAddress(): Pair<Inet4Address?, String> {
        val network = connectivity.activeNetwork ?: return null to "The TV isn't connected to a network"
        val addresses = connectivity.ipv4Addresses(network)
        val usable = addresses.firstOrNull { !it.isLinkLocalAddress }
        return when {
            usable != null -> usable to ""
            addresses.isNotEmpty() ->
                null to "Self-assigned address ${addresses.first().hostAddress}: no answer from DHCP yet"
            else -> null to "Connected, but no IP address yet"
        }
    }

    private fun onLive() {
        status.lostAt?.let { lostAt ->
            AppLog.i(TAG, "Player $logId picture back after ${status.retries} retries, ${(System.currentTimeMillis() - lostAt) / 1000} s")
        }
        // Already live: the picture moved to or from full screen
        if (status.live) {
            AppLog.i(TAG, "Player $logId picture on a new surface")
        } else {
            AppLog.i(TAG, "Player $logId live after ${SystemClock.elapsedRealtime() - attemptStartedAt} ms")
        }
        quietRetries = 0
        status.reset(Phase.Live)
        lastFrames = renderedFrames()
        lastProgressAt = SystemClock.elapsedRealtime()
        liveAt = lastProgressAt
        lastPictureCheckAt = lastProgressAt
        pictureSeen = false
        nextSnapshotAt = lastProgressAt + FIRST_SNAPSHOT_DELAY_MS
        settledCopyDone = false
    }

    private fun onStreamError(error: PlaybackException) {
        // A release that timed out lands here: nothing to retry, this connection is over
        if (released || replacingPlayer) {
            AppLog.w(TAG, "Player $logId while releasing: ${error.errorCodeName}", error)
            return
        }
        // Another player's decoder may just be closing: not worth an error on screen yet
        val noDecoder = error.errorCode == PlaybackException.ERROR_CODE_DECODER_INIT_FAILED ||
            error.errorCode == PlaybackException.ERROR_CODE_DECODING_FAILED
        if (decodersTakeTurns && noDecoder && !status.live && quietRetries < MAX_QUIET_RETRIES) {
            quietRetries += 1
            AppLog.i(TAG, "Player $logId got no decoder, quiet retry $quietRetries")
            player.stop()
            handler.postDelayed(attempt, QUIET_RETRY_DELAY_MS)
            return
        }
        if (refusedDescription(error)) {
            lose(describeMissingFormat(tracks, useAudio), unreachable = false, retryDelay = DESCRIPTION_RETRY_DELAY_MS)
            return
        }
        val unreachable = generateSequence<Throwable>(error) { it.cause }
            .any { it is SocketTimeoutException || it is ConnectException || it is NoRouteToHostException }
        lose(describe(error), unreachable)
    }

    /**
     * [unreachable]: the camera couldn't be reached, so try again soon. [stalledFor]: how long the
     * picture had already been stuck when this was noticed. [retryDelay] overrides the usual delays.
     */
    private fun lose(reason: String, unreachable: Boolean, stalledFor: Long = 0, retryDelay: Long? = null) {
        if (status.phase != Phase.Live && status.phase != Phase.Connecting) return
        val now = SystemClock.elapsedRealtime()
        // It reached the camera and still lost the picture. Otherwise, the next try can use it again
        if (status.live || status.cameraAnswered != null) needsNewPlayer = true
        if (status.live) {
            val lostAt = System.currentTimeMillis() - stalledFor
            // Copied before stopping, while the last frame is still there
            snapshots.capture(video, handler, takenAt = lostAt)
            snapshots.logCopies()
            status.lost(lostAt)
        } else {
            status.lost(System.currentTimeMillis() - (now - attemptStartedAt))
        }
        status.lastError = reason
        // Video came, but the audio it waits for didn't
        val audioCame = (player.audioDecoderCounters?.queuedInputBufferCount ?: 0) > 0
        val videoCame = (player.videoDecoderCounters?.queuedInputBufferCount ?: 0) > 0
        if (withAudio && !silentAudio && videoCame && !audioCame) {
            AppLog.i(TAG, "Player $logId: the camera sends no audio, going on without it")
            silentAudio = true
            player.applyAudio()
        }
        player.stop()
        val delay = when {
            retryDelay != null -> retryDelay
            unreachable -> (UNREACHABLE_RETRY_INTERVAL_MS - (now - attemptStartedAt)).coerceAtLeast(0)
            else -> RETRY_DELAY_MS
        }
        AppLog.i(TAG, "Player $logId no picture: $reason. Retries so far: ${status.retries}, next in $delay ms")
        status.phase = Phase.RetryScheduled
        status.nextRetryAt = now + delay
        handler.postDelayed(attempt, delay)
    }

    // Not the playback position: with no audio that runs on its own clock, even if no frame comes out
    private fun renderedFrames() = player.videoDecoderCounters?.renderedOutputBufferCount ?: 0

    /** Until a real picture shows, looks at what's on screen: the player can say it plays over a black surface */
    private fun checkBlackPicture(now: Long) {
        // Any good copy so far proves that copies work on this TV: a black one then really means black
        if (pictureSeen || latestSnapshots.isEmpty() || now - lastPictureCheckAt < BLACK_PICTURE_CHECK_INTERVAL_MS) return
        lastPictureCheckAt = now
        snapshots.capture(video, handler, save = false) { black ->
            if (!black) {
                pictureSeen = true
            } else if (status.live && !pictureSeen && SystemClock.elapsedRealtime() - liveAt > BLACK_PICTURE_TIMEOUT_MS) {
                lose("The picture stayed black for ${BLACK_PICTURE_TIMEOUT_MS / 1000} s", unreachable = false)
            }
        }
    }

    private fun copyPicture(now: Long) {
        val settled = now - liveAt >= SETTLED_SNAPSHOT_DELAY_MS
        val save = !settledCopyDone || now - lastSavedAt >= SNAPSHOT_SAVE_INTERVAL_MS
        snapshots.capture(video, handler, save = save)
        if (save) lastSavedAt = now
        if (settled) settledCopyDone = true
        nextSnapshotAt = if (settled) now + snapshotInterval else liveAt + SETTLED_SNAPSHOT_DELAY_MS
    }

    private fun check() {
        // Keep close to live: speed up while too much is buffered
        val behind = player.bufferedPosition - player.currentPosition
        when {
            behind > BEHIND_LIMIT_MS -> player.setPlaybackSpeed(CATCH_UP_SPEED)
            behind < CAUGHT_UP_MS -> player.setPlaybackSpeed(1f)
        }

        val now = SystemClock.elapsedRealtime()
        when (status.phase) {
            Phase.Live -> {
                // Watchdog: a camera that stops sending raises no error, the last frame just stays on screen
                checkBlackPicture(now)
                val frames = renderedFrames()
                if (frames != lastFrames) {
                    lastFrames = frames
                    lastProgressAt = now
                    if (now >= nextSnapshotAt) copyPicture(now)
                } else if (now - lastProgressAt > FROZEN_TIMEOUT_MS) {
                    lose("The picture froze for ${FROZEN_TIMEOUT_MS / 1000} s", unreachable = true, stalledFor = now - lastProgressAt)
                }
            }
            Phase.Connecting -> if (now - attemptStartedAt > CONNECT_TIMEOUT_MS) {
                lose(
                    if (anyPlayerStuck) {
                        STUCK_PLAYER_MESSAGE
                    } else if (status.cameraAnswered != null) {
                        "The camera answered, but no picture came within ${CONNECT_TIMEOUT_MS / 1000} s"
                    } else {
                        "No answer from the camera within ${CONNECT_TIMEOUT_MS / 1000} s"
                    },
                    unreachable = false,
                )
            }
            else -> Unit
        }
    }
}

/** What went wrong, in plain words, with what to check where it helps; addresses keep no password */
private fun describe(error: PlaybackException): String {
    val causes = generateSequence<Throwable>(error) { it.cause }.toList()
    fun mentions(code: String) = causes.any { it.message?.contains(code) == true }
    val reason = when {
        causes.any { it is SocketTimeoutException } ->
            "The camera didn't answer within ${SOCKET_CONNECT_TIMEOUT_MS / 1000} s: it's off, or the network can't reach it"
        causes.any { it is UnknownHostException } -> "The camera's name couldn't be found (DNS): try its IP address"
        mentions("ECONNREFUSED") -> "The camera refused the connection: wrong port, or RTSP turned off on the camera"
        mentions("EHOSTUNREACH") || causes.any { it is NoRouteToHostException } ->
            "No route to the camera: it's off, or the network can't reach it"
        mentions("ENETUNREACH") -> "The TV's network can't reach the camera's network"
        causes.any { it is ConnectException } -> "Can't connect to the camera"
        else -> describeRtsp(causes) ?: when (error.errorCode) {
            PlaybackException.ERROR_CODE_DECODER_INIT_FAILED,
            PlaybackException.ERROR_CODE_DECODER_QUERY_FAILED,
            PlaybackException.ERROR_CODE_DECODING_FAILED,
            PlaybackException.ERROR_CODE_DECODING_FORMAT_EXCEEDS_CAPABILITIES,
            PlaybackException.ERROR_CODE_DECODING_FORMAT_UNSUPPORTED ->
                if (anyPlayerStuck) {
                    STUCK_PLAYER_MESSAGE
                } else {
                    "This TV has no free video decoder, or can't play this camera's video"
                }
            else -> "Playback error: " + (causes.last().message ?: error.errorCodeName)
        }
    }
    return reason.replace(Regex("""(rtsps?://)[^/@\s]*@"""), "$1***@").take(140)
}

/** Media3 refused the camera's description of its stream, e.g. "missing attribute fmtp" */
private fun refusedDescription(error: PlaybackException) = generateSequence<Throwable>(error) { it.cause }
    .any { cause -> cause.message.orEmpty().let { "missing attribute fmtp" in it || "sprop" in it } }

/** Which track the camera left without its format, and what to do about it */
private fun describeMissingFormat(tracks: List<SdpTrack>?, useAudio: Boolean): String {
    val video = tracks?.firstOrNull { it.media == "video" && !it.described }
    val audio = tracks?.firstOrNull { it.media == "audio" && !it.described }
    return when {
        video != null -> {
            val codec = when (video.encoding) {
                "H264" -> "H.264"
                "H265" -> "H.265"
                else -> video.encoding
            }
            "The camera leaves out its $codec video's format, which this player needs. A restream " +
                "(e.g. Frigate's, or the go2rtc add-on for Home Assistant) can add it for you"
        }
        audio != null && useAudio ->
            "The camera leaves out its audio track's format, so the stream can't play. Turn off \"Use audio track\" in the camera's settings"
        else -> "The camera's description of its stream is incomplete, so it can't play"
    }
}

private val CAMERA_AUDIO = AudioAttributes.Builder().setUsage(C.USAGE_MEDIA).setContentType(C.AUDIO_CONTENT_TYPE_MOVIE).build()

/** The camera's RTSP answer, e.g. "SETUP 401", in plain words */
private fun describeRtsp(causes: List<Throwable>): String? {
    val message = causes.firstOrNull { it is RtspMediaSource.RtspPlaybackException }?.message ?: return null
    return when (Regex("""\b\d{3}\b""").find(message)?.value) {
        "401" -> "The camera refused the login: check the user name and password"
        "403" -> "The camera refused access to this stream (403)"
        "404" -> "The camera has no stream at this address: check the part after the port (404)"
        "454" -> "The camera dropped the session (454)"
        "461" -> "The camera doesn't support this transport: try TCP (461)"
        "503" -> "The camera is busy, maybe too many viewers (503)"
        else -> "The camera answered: $message"
    }
}

/** e.g. "H.265 2560×1440" */
private fun describeVideo(format: Format): String {
    val codec = when (format.sampleMimeType) {
        MimeTypes.VIDEO_H265 -> "H.265"
        MimeTypes.VIDEO_H264 -> "H.264"
        else -> format.sampleMimeType?.substringAfter('/')?.uppercase() ?: "video"
    }
    return if (format.width > 0 && format.height > 0) "$codec ${format.width}×${format.height}" else codec
}

/**
 * Gives up connecting after a couple of seconds instead of the system's minutes (see
 * SOCKET_CONNECT_TIMEOUT_MS), and shows the camera's stream description to [onDescription], which
 * may change it before the player reads it.
 */
private class CameraSocketFactory(private val onDescription: (String) -> String) : SocketFactory() {
    private fun connect(address: InetSocketAddress, local: InetSocketAddress? = null) =
        createSocket().apply {
            if (local != null) bind(local)
            connect(address, SOCKET_CONNECT_TIMEOUT_MS)
        }

    override fun createSocket(): Socket = DescribedSocket(onDescription)
    override fun createSocket(host: String, port: Int) = connect(InetSocketAddress(host, port))
    override fun createSocket(host: InetAddress, port: Int) = connect(InetSocketAddress(host, port))
    override fun createSocket(host: String, port: Int, localHost: InetAddress, localPort: Int) =
        connect(InetSocketAddress(host, port), InetSocketAddress(localHost, localPort))
    override fun createSocket(address: InetAddress, port: Int, localAddress: InetAddress, localPort: Int) =
        connect(InetSocketAddress(address, port), InetSocketAddress(localAddress, localPort))
}

private class DescribedSocket(private val onDescription: (String) -> String) : Socket() {
    private val filtered by lazy { RtspFilterStream(rawInput(), onDescription) }

    private fun rawInput(): InputStream = super.getInputStream()

    override fun getInputStream(): InputStream = filtered
}

class Snapshot(val bitmap: Bitmap, val takenAt: Long) {
    val image: ImageBitmap = bitmap.asImageBitmap()
}

/** Each camera's last picture by address, shared by the main view and the thumbnails */
private val latestSnapshots = mutableStateMapOf<String, Snapshot>()

// Named after the address, so a camera never shows another one's picture (the address itself isn't stored)
private fun snapshotFile(dir: File, url: String) = File(dir, "camera_${Integer.toHexString(url.hashCode())}.jpg")

/** A camera's last picture, from memory or else from the app's files; null if it never had one */
@Composable
fun cameraSnapshot(url: String): Snapshot? {
    val dir = LocalContext.current.filesDir
    LaunchedEffect(url) { loadSnapshot(dir, url) }
    return latestSnapshots[url]
}

private suspend fun loadSnapshot(dir: File, url: String) {
    if (latestSnapshots[url] != null) return
    val file = snapshotFile(dir, url)
    val loaded = withContext(Dispatchers.IO) {
        BitmapFactory.decodeFile(file.path)?.let { Snapshot(it, file.lastModified()) }
    }
    // A picture taken meanwhile is newer
    if (loaded != null && latestSnapshots[url] == null) latestSnapshots[url] = loaded
}

/** Deletes the pictures of cameras that were removed or whose address changed */
fun pruneCameraSnapshots(context: Context, urls: List<String>) {
    latestSnapshots.keys.retainAll(urls.toSet())
    val keep = urls.map { snapshotFile(context.filesDir, it).name }.toSet()
    thread(name = "camera-snapshot") {
        context.filesDir.listFiles { f -> f.name.startsWith("camera_") && f.name.endsWith(".jpg") && f.name !in keep }
            ?.forEach { it.delete() }
    }
}

// A copy can take 300 ms on older TVs, and holds up the thread that asks for it
private val pictureCopying = Executors.newSingleThreadExecutor { task -> Thread(task, "camera-picture-copy").apply { isDaemon = true } }

/** One camera's last picture, kept in the app's private files so it survives restarts and standby. */
private class SnapshotStore(private val dir: File, private val url: String) {
    private val file = snapshotFile(dir, url)

    val snapshot get() = latestSnapshots[url]

    private var saved: Snapshot? = null

    // Copies since the last logCopies()
    private var copied = 0
    private var black = 0
    private var failed = 0
    private var lastFailure = PixelCopy.SUCCESS

    suspend fun load() = loadSnapshot(dir, url)

    /** Copies the frame on screen from the video layer, while it's visible; with [save], also to disk */
    fun capture(
        video: SurfaceView,
        handler: Handler,
        takenAt: Long = System.currentTimeMillis(),
        save: Boolean = true,
        onCopied: (black: Boolean) -> Unit = {},
    ) {
        if (!video.holder.surface.isValid || video.width == 0) return
        val bitmap = Bitmap.createBitmap(SNAPSHOT_WIDTH, SNAPSHOT_WIDTH * video.height / video.width, Bitmap.Config.ARGB_8888)
        val onResult = PixelCopy.OnPixelCopyFinishedListener { result ->
            // A copy can come back black, e.g. while something covers the video; the previous picture is kept
            when {
                result != PixelCopy.SUCCESS -> {
                    failed++
                    lastFailure = result
                }
                bitmap.isBlack() -> {
                    black++
                    onCopied(true)
                }
                else -> {
                    copied++
                    latestSnapshots[url] = Snapshot(bitmap, takenAt)
                    if (save) save()
                    onCopied(false)
                }
            }
        }
        pictureCopying.execute {
            try {
                PixelCopy.request(video, bitmap, onResult, handler)
            } catch (e: IllegalArgumentException) {
                // The surface went away just before the copy
                handler.post { onResult.onPixelCopyFinished(PixelCopy.ERROR_SOURCE_NO_DATA) }
            }
        }
    }

    /** Logs how the copies went since the last call, e.g. when the picture is lost or the launcher stops */
    fun logCopies() {
        if (copied + black + failed == 0) return
        AppLog.i(
            TAG,
            "Picture copies: $copied ok, $black black, $failed failed" +
                if (failed > 0) " (last error $lastFailure)" else "",
        )
        copied = 0
        black = 0
        failed = 0
    }

    /** Writes the latest copy to disk, if not done yet */
    fun save() {
        val current = snapshot ?: return
        if (current === saved) return
        saved = current
        thread(name = "camera-snapshot") {
            file.outputStream().use { current.bitmap.compress(Bitmap.CompressFormat.JPEG, 85, it) }
            file.setLastModified(current.takenAt)
        }
    }
}

/** True when a sample of pixels is all (near) black */
private fun Bitmap.isBlack(): Boolean {
    for (y in 0 until 8) for (x in 0 until 8) {
        val pixel = getPixel(x * (width - 1) / 7, y * (height - 1) / 7)
        if ((pixel shr 16 and 0xff) > 8 || (pixel shr 8 and 0xff) > 8 || (pixel and 0xff) > 8) return false
    }
    return true
}

/** What's going on and any error, on a small view */
@Composable
private fun CompactCameraStatus(status: ConnectionStatus) {
    Column(
        modifier = Modifier
            .padding(8.dp)
            .background(Color.Black.copy(alpha = 0.7f), RoundedCornerShape(8.dp))
            .padding(horizontal = 8.dp, vertical = 4.dp),
        horizontalAlignment = Alignment.CenterHorizontally,
    ) {
        Text(
            when {
                status.waitingForDecoders -> "Waiting for a decoder…"
                status.phase == Phase.WaitingForNetwork -> "Network down"
                status.lostAt != null -> "Substream offline"
                else -> "Connecting…"
            },
            style = MaterialTheme.typography.labelMedium,
            color = MaterialTheme.colorScheme.onSurface,
        )
        status.lastError?.let {
            Text(it, style = MaterialTheme.typography.labelSmall, color = ErrorColor, maxLines = 2, overflow = TextOverflow.Ellipsis)
        }
    }
}

@Composable
private fun CameraStatus(status: ConnectionStatus, snapshotTakenAt: Long?) {
    // Ticks for the countdown to the next retry
    val now by produceState(SystemClock.elapsedRealtime()) {
        while (true) {
            value = SystemClock.elapsedRealtime()
            delay(250)
        }
    }
    val lostAt = status.lostAt
    val retries = when (status.retries) {
        0 -> null
        1 -> "1 retry so far"
        else -> "${status.retries} retries so far"
    }
    val title = when {
        status.waitingForDecoders -> "Waiting for other decoders to release…"
        status.phase == Phase.WaitingForNetwork -> "Network down"
        lostAt != null -> "Camera offline since ${formatTime(lostAt)}"
        else -> "Connecting to camera…"
    }
    val step = if (status.waitingForDecoders) "" else when (status.phase) {
        Phase.WaitingForNetwork -> "${status.networkProblem} · checking every ${NETWORK_CHECK_INTERVAL_MS} ms"
        Phase.Connecting -> {
            val answered = status.cameraAnswered
            val action = when {
                answered == null -> "Contacting the camera at ${status.cameraHost}…"
                answered.isEmpty() -> "Camera answered · waiting for the first picture…"
                else -> "Camera answered · waiting for the first picture ($answered)…"
            }
            if (status.retries > 0) "Retry ${status.retries} · $action" else action
        }
        Phase.RetryScheduled -> (status.nextRetryAt - now).let { left ->
            listOfNotNull(retries, if (left < 1_000) "retrying now…" else "next retry in ${(left + 999) / 1000} s").joinToString(" · ")
        }
        Phase.Live -> ""
    }
    // While the network is down, when the picture was lost isn't in the title
    val offlineSince = lostAt?.takeIf { status.phase == Phase.WaitingForNetwork }?.let { "Camera offline since ${formatTime(it)}" }

    // On a dark chip: it sits over the dimmed last picture
    Column(
        modifier = Modifier
            .background(Color.Black.copy(alpha = 0.7f), RoundedCornerShape(8.dp))
            .padding(horizontal = 16.dp, vertical = 8.dp),
        horizontalAlignment = Alignment.CenterHorizontally,
    ) {
        Text(title, style = MaterialTheme.typography.titleMedium, color = MaterialTheme.colorScheme.onSurface)
        if (step.isNotEmpty()) Text(step, style = MaterialTheme.typography.bodyMedium, color = MaterialTheme.colorScheme.onSurface)
        // The last error stays up through the retries, until the picture is back
        status.lastError?.let {
            Text(it, style = MaterialTheme.typography.bodySmall, color = ErrorColor)
        }
        offlineSince?.let {
            Text(it, style = MaterialTheme.typography.bodySmall, color = MaterialTheme.colorScheme.onSurfaceVariant)
        }
        // Unless it's the moment the picture was lost, already shown above
        snapshotTakenAt?.takeIf { lostAt == null || abs(it - lostAt) > 2_000 }?.let {
            Text("Picture from ${formatTime(it)}", style = MaterialTheme.typography.bodySmall, color = MaterialTheme.colorScheme.onSurfaceVariant)
        }
    }
}

/** 16:18:05 today, otherwise with the date */
private fun formatTime(epochMillis: Long): String {
    val time = Instant.ofEpochMilli(epochMillis).atZone(ZoneId.systemDefault())
    val pattern = if (time.toLocalDate() == LocalDate.now()) "HH:mm:ss" else "d MMM HH:mm"
    return time.format(DateTimeFormatter.ofPattern(pattern))
}
