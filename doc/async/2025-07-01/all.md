# src/Init/System/ST.lean

```python
def EStateM (ε σ α : Type u) := σ → Result ε σ α # src/Init/Prelude

@[expose] def EST (ε : Type) (σ : Type) : Type → Type := EStateM ε σ := σ → Result ε σ α
abbrev ST (σ : Type) := EST Empty σ
# instance (ε σ : Type) : Monad (EST ε σ) :=
# instance (ε σ : Type) : MonadExceptOf ε (EST ε σ) :=
# instance {ε σ : Type} {α : Type} [Inhabited ε] : Inhabited (EST ε σ α) :=
# instance (σ : Type) : Monad (ST σ) :=
class STWorld (σ : outParam Type) (m : Type → Type)
  instance {σ m n} [MonadLift m n] [STWorld σ m] : STWorld σ n := ⟨⟩
  instance {ε σ} : STWorld σ (EST ε σ) := ⟨⟩
def runEST {ε α : Type} (x : (σ : Type) → EST ε σ α) : Except ε α :=
def runST {α : Type} (x : (σ : Type) → ST σ α) : α :=
  instance {ε σ} : MonadLift (ST σ) (EST ε σ) :=
namespace ST
  instance {σ α} [s : Nonempty α] : Nonempty (Ref σ α) :=
  namespace Prim
    @[extern "lean_st_mk_ref"] opaque mkRef {σ α} (a : α) : ST σ (Ref σ α)
    @[extern "lean_st_ref_get"] opaque Ref.get {σ α} (r : @& Ref σ α) : ST σ α
    @[extern "lean_st_ref_set"] opaque Ref.set {σ α} (r : @& Ref σ α) (a : α) : ST σ Unit
    @[extern "lean_st_ref_swap"] opaque Ref.swap {σ α} (r : @& Ref σ α) (a : α) : ST σ α
    @[extern "lean_st_ref_take"] unsafe opaque Ref.take {σ α} (r : @& Ref σ α) : ST σ α
    @[extern "lean_st_ref_ptr_eq"] opaque Ref.ptrEq {σ α} (r1 r2 : @& Ref σ α) : ST σ Bool
    def Ref.modify {σ α : Type} (r : Ref σ α) (f : α → α) : ST σ Unit := do
    def Ref.modifyGet {σ α β : Type} (r : Ref σ α) (f : α → β × α) : ST σ β := do
  end Prim

  section
    variable {σ : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST σ) m]

    @[inline] def mkRef {α : Type} (a : α) : m (Ref σ α) :=  liftM <| Prim.mkRef a
    @[inline] def Ref.get {α : Type} (r : Ref σ α) : m α := liftM <| Prim.Ref.get r
    @[inline] def Ref.set {α : Type} (r : Ref σ α) (a : α) : m Unit := liftM <| Prim.Ref.set r a
    @[inline] def Ref.swap {α : Type} (r : Ref σ α) (a : α) : m α := liftM <| Prim.Ref.swap r a
    @[inline] unsafe def Ref.take {α : Type} (r : Ref σ α) : m α := liftM <| Prim.Ref.take r
    @[inline] def Ref.ptrEq {α : Type} (r1 r2 : Ref σ α) : m Bool := liftM <| Prim.Ref.ptrEq r1 r2
    @[inline] def Ref.modify {α : Type} (r : Ref σ α) (f : α → α) : m Unit := liftM <| Prim.Ref.modify r f
    @[inline] def Ref.modifyGet {α : Type} {β : Type} (r : Ref σ α) (f : α → β × α) : m β := liftM <| Prim.Ref.modifyGet r f
    def Ref.toMonadStateOf (r : Ref σ α) : MonadStateOf α m where
  end
end ST
```

# src/Init/Task.lean

```python
namespace Task
  def mapList (f : List α → β) (tasks : List (Task α)) (prio := Task.Priority.default) (sync := false) : Task β :=
```

# src/Init/Core.lean

```python
structure Task (α : Type u) : Type u where
  pure ::
  get : α
  deriving Inhabited, Nonempty

attribute [extern "lean_task_pure"] Task.pure
attribute [extern "lean_task_get_own"] Task.get
namespace Task
  @[extern "lean_task_spawn"] protected def spawn {α : Type u} (fn : Unit → α) (prio := Priority.default) : Task α :=
  @[extern "lean_task_map"] protected def map (f : α → β) (x : Task α) (prio := Priority.default) (sync := false) : Task β :=
  @[extern "lean_task_bind"] protected def bind (x : Task α) (f : α → Task β) (prio := Priority.default) (sync := false) :
end Task
```

# src/Init/System/IO.lean

```python
@[expose] def IO.RealWorld : Type := Unit
@[expose] def EIO (ε : Type) : Type → Type := EStateM ε IO.RealWorld
# instance : Monad (EIO ε) := inferInstanceAs (Monad (EStateM ε IO.RealWorld))
# instance : MonadFinally (EIO ε) := inferInstanceAs (MonadFinally (EStateM ε IO.RealWorld))
# instance : MonadExceptOf ε (EIO ε) := inferInstanceAs (MonadExceptOf ε (EStateM ε IO.RealWorld))
# instance : OrElse (EIO ε α) := ⟨MonadExcept.orElse⟩
# instance [Inhabited ε] : Inhabited (EIO ε α) := inferInstanceAs (Inhabited (EStateM ε IO.RealWorld α))
@[expose] def BaseIO := EIO Empty
# instance : Monad BaseIO := inferInstanceAs (Monad (EIO Empty))
# instance : MonadFinally BaseIO := inferInstanceAs (MonadFinally (EIO Empty))
def BaseIO.toEIO (act : BaseIO α) : EIO ε α :=
# instance : MonadLift BaseIO (EIO ε) := ⟨BaseIO.toEIO⟩
def EIO.toBaseIO (act : EIO ε α) : BaseIO (Except ε α) :=
def EIO.catchExceptions (act : EIO ε α) (h : ε → BaseIO α) : BaseIO α :=
def EIO.ofExcept (e : Except ε α) : EIO ε α :=
abbrev IO : Type → Type := EIO Error
def BaseIO.toIO (act : BaseIO α) : IO α :=
def EIO.toIO (f : ε → IO.Error) (act : EIO ε α) : IO α :=
def EIO.toIO' (act : EIO ε α) : IO (Except ε α) :=
def IO.toEIO (f : IO.Error → ε) (act : IO α) : EIO ε α :=
unsafe def unsafeBaseIO (fn : BaseIO α) : α :=
unsafe def unsafeEIO (fn : EIO ε α) : Except ε α :=
unsafe def unsafeIO (fn : IO α) : Except IO.Error α :=
# @[extern "lean_io_timeit"] opaque timeit (msg : @& String) (fn : IO α) : IO α
# @[extern "lean_io_allocprof"] opaque allocprof (msg : @& String) (fn : IO α) : IO α
# @[extern "lean_io_initializing"] opaque IO.initializing : BaseIO Bool
namespace BaseIO
  @[extern "lean_io_as_task"] opaque asTask (act : BaseIO α) (prio := Task.Priority.default) : BaseIO (Task α) :=
  @[extern "lean_io_map_task"] opaque mapTask (f : α → BaseIO β) (t : Task α) (prio := Task.Priority.default) (sync := false) : BaseIO (Task β) :=
  @[extern "lean_io_bind_task"] opaque bindTask (t : Task α) (f : α → BaseIO (Task β)) (prio := Task.Priority.default) (sync := false) : BaseIO (Task β) :=
  def chainTask (t : Task α) (f : α → BaseIO Unit) (prio := Task.Priority.default) (sync := false) : BaseIO Unit :=
  def mapTasks (f : List α → BaseIO β) (tasks : List (Task α)) (prio := Task.Priority.default) (sync := false) : BaseIO (Task β) :=
end BaseIO
namespace EIO
  def asTask (act : EIO ε α) (prio := Task.Priority.default) : BaseIO (Task (Except ε α)) :=
  def mapTask (f : α → EIO ε β) (t : Task α) (prio := Task.Priority.default) (sync := false) : BaseIO (Task (Except ε β)) :=
  def bindTask (t : Task α) (f : α → EIO ε (Task (Except ε β))) (prio := Task.Priority.default) (sync := false) : BaseIO (Task (Except ε β)) :=
  def chainTask (t : Task α) (f : α → EIO ε Unit) (prio := Task.Priority.default) (sync := false) : EIO ε Unit :=
  def mapTasks (f : List α → EIO ε β) (tasks : List (Task α)) (prio := Task.Priority.default) (sync := false) : BaseIO (Task (Except ε β)) :=
end EIO
namespace IO
  # def ofExcept [ToString ε] (e : Except ε α) : IO α :=
  # def lazyPure (fn : Unit → α) : IO α :=
  # @[extern "lean_io_mono_ms_now"] opaque monoMsNow : BaseIO Nat
  # @[extern "lean_io_mono_nanos_now"] opaque monoNanosNow : BaseIO Nat
  # @[extern "lean_io_get_random_bytes"] opaque getRandomBytes (nBytes : USize) : IO ByteArray
  # def sleep (ms : UInt32) : BaseIO Unit :=
              # `act` and `f` should use `IO.checkCanceled`
  def asTask (act : IO α) (prio := Task.Priority.default) : BaseIO (Task (Except IO.Error α)) :=
  def mapTask (f : α → IO β) (t : Task α) (prio := Task.Priority.default) (sync := false) : BaseIO (Task (Except IO.Error β)) :=
  def bindTask (t : Task α) (f : α → IO (Task (Except IO.Error β))) (prio := Task.Priority.default) (sync := false) : BaseIO (Task (Except IO.Error β)) :=
  def chainTask (t : Task α) (f : α → IO Unit) (prio := Task.Priority.default) (sync := false) : IO Unit :=

  @[extern "lean_io_check_canceled"] opaque checkCanceled : BaseIO Bool
  @[extern "lean_io_cancel"] opaque cancel : @& Task α → BaseIO Unit
    inductive TaskState | waiting | running | finished
    instance : ToString TaskState := ⟨TaskState.toString⟩
  @[extern "lean_io_get_task_state"] opaque getTaskState : @& Task α → BaseIO TaskState
  def hasFinished (task : Task α) : BaseIO Bool := do
  @[extern "lean_io_wait"] opaque wait (t : Task α) : BaseIO α := # this func is stupid, same as `return t.get`
  @[extern "lean_io_wait_any"] opaque waitAny (tasks : @& List (Task α)) (h : tasks.length > 0 := by exact Nat.zero_lt_succ _) : BaseIO α :=
  # @[extern "lean_io_get_num_heartbeats"] opaque getNumHeartbeats : BaseIO Nat
  # @[extern "lean_io_set_heartbeats"] opaque setNumHeartbeats (count : Nat) : BaseIO Unit
  # def addHeartbeats (count : Nat) : BaseIO Unit := do
    # inductive FS.Mode where | read ...
  # opaque FS.Handle : Type := Unit
  # @[extern "lean_get_stdin"] opaque getStdin  : BaseIO FS.Stream
  # @[extern "lean_get_stdout"] opaque getStdout : BaseIO FS.Stream
  # @[extern "lean_get_stderr"] opaque getStderr : BaseIO FS.Stream
  # @[extern "lean_get_set_stdin"] opaque setStdin  : FS.Stream → BaseIO FS.Stream
  # @[extern "lean_get_set_stdout"] opaque setStdout : FS.Stream → BaseIO FS.Stream
  # @[extern "lean_get_set_stderr"] opaque setStderr : FS.Stream → BaseIO FS.Stream
  # @[specialize] partial def iterate (a : α) (f : α → IO (Sum α β)) : IO β := do

  # namespace FS
  #   namespace Handle
  #     @[extern "lean_io_prim_handle_mk"] opaque mk (fn : @& FilePath) (mode : FS.Mode) : IO Handle
  #     @[extern "lean_io_prim_handle_lock"] opaque lock (h : @& Handle) (exclusive := true) : IO Unit
  #     @[extern "lean_io_prim_handle_try_lock"] opaque tryLock (h : @& Handle) (exclusive := true) : IO Bool
  #     @[extern "lean_io_prim_handle_unlock"] opaque unlock (h : @& Handle) : IO Unit
  #     @[extern "lean_io_prim_handle_is_tty"] opaque isTty (h : @& Handle) : BaseIO Bool
  #     @[extern "lean_io_prim_handle_flush"] opaque flush (h : @& Handle) : IO Unit
  #     @[extern "lean_io_prim_handle_rewind"] opaque rewind (h : @& Handle) : IO Unit
  #     @[extern "lean_io_prim_handle_truncate"] opaque truncate (h : @& Handle) : IO Unit
  #     @[extern "lean_io_prim_handle_read"] opaque read (h : @& Handle) (bytes : USize) : IO ByteArray
  #     @[extern "lean_io_prim_handle_write"] opaque write (h : @& Handle) (buffer : @& ByteArray) : IO Unit
  #     @[extern "lean_io_prim_handle_get_line"] opaque getLine (h : @& Handle) : IO String
  #     @[extern "lean_io_prim_handle_put_str"] opaque putStr (h : @& Handle) (s : @& String) : IO Unit
  #   end Handle
  #   @[extern "lean_io_realpath"] opaque realPath (fname : FilePath) : IO FilePath
  #   @[extern "lean_io_remove_file"] opaque removeFile (fname : @& FilePath) : IO Unit
  #   @[extern "lean_io_remove_dir"] opaque removeDir : @& FilePath → IO Unit
  #   @[extern "lean_io_create_dir"] opaque createDir : @& FilePath → IO Unit
  #   @[extern "lean_io_rename"] opaque rename (old new : @& FilePath) : IO Unit
  #   @[extern "lean_io_create_tempfile"] opaque createTempFile : IO (Handle × FilePath)
  #   @[extern "lean_io_create_tempdir"] opaque createTempDir : IO FilePath
  # end FS
  # @[extern "lean_io_getenv"] opaque getEnv (var : @& String) : BaseIO (Option String)
  # @[extern "lean_io_app_path"] opaque appPath : IO FilePath
  # @[extern "lean_io_current_dir"] opaque currentDir : IO FilePath
  # namespace FS
  #   def withFile (fn : FilePath) (mode : Mode) (f : Handle → IO α) : IO α :=
  #   def Handle.putStrLn (h : Handle) (s : String) : IO Unit :=
  #   partial def Handle.readBinToEndInto (h : Handle) (buf : ByteArray) : IO ByteArray := do
  #   def Handle.readBinToEnd (h : Handle) : IO ByteArray := do
  #   def Handle.readToEnd (h : Handle) : IO String := do
  #   partial def Handle.lines (h : Handle) : IO (Array String) := do
  #   def lines (fname : FilePath) : IO (Array String) := do
  #   def writeBinFile (fname : FilePath) (content : ByteArray) : IO Unit := do
  #   def writeFile (fname : FilePath) (content : String) : IO Unit := do
  #   def Stream.putStrLn (strm : FS.Stream) (s : String) : IO Unit :=
  #   def DirEntry.path (entry : DirEntry) : FilePath :=
  #   instance : LT SystemTime := ltOfOrd
  #   instance : LE SystemTime := leOfOrd
  # end FS
end IO
# namespace System.FilePath
#   @[extern "lean_io_read_dir"] opaque readDir : @& FilePath → IO (Array IO.FS.DirEntry)
#   @[extern "lean_io_metadata"] opaque metadata : @& FilePath → IO IO.FS.Metadata
#   @[extern "lean_io_symlink_metadata"] opaque symlinkMetadata : @& FilePath → IO IO.FS.Metadata
#   def isDir (p : FilePath) : BaseIO Bool := do
#   def pathExists (p : FilePath) : BaseIO Bool :=
#   partial def walkDir (p : FilePath) (enter : FilePath → IO Bool := fun _ => pure true) : IO (Array FilePath) :=
# end System.FilePath
namespace IO
  # namespace FS
  #   def readBinFile (fname : FilePath) : IO ByteArray := do
  #   def readFile (fname : FilePath) : IO String := do
  # end FS
  # def withStdin [Monad m] [MonadFinally m] [MonadLiftT BaseIO m] (h : FS.Stream) (x : m α) : m α := do
  # def withStdout [Monad m] [MonadFinally m] [MonadLiftT BaseIO m] (h : FS.Stream) (x : m α) : m α := do
  # def withStderr [Monad m] [MonadFinally m] [MonadLiftT BaseIO m] (h : FS.Stream) (x : m α) : m α := do
  # def print [ToString α] (s : α) : IO Unit := do
  # def println [ToString α] (s : α) : IO Unit :=
  # def eprint [ToString α] (s : α) : IO Unit := do
  # def eprintln [ToString α] (s : α) : IO Unit :=
  # def appDir : IO FilePath := do
  # namespace FS
  #   partial def createDirAll (p : FilePath) : IO Unit := do
  #   partial def removeDirAll (p : FilePath) : IO Unit := do
  #   def withTempFile [Monad m] [MonadFinally m] [MonadLiftT IO m] (f : Handle → FilePath → m α) :
  #   def withTempDir [Monad m] [MonadFinally m] [MonadLiftT IO m] (f : FilePath → m α) :
  # end FS
  # namespace Process
  #   @[extern "lean_io_process_set_current_dir"] opaque setCurrentDir (path : @& FilePath) : IO Unit
  #   @[expose] def Stdio.toHandleType : Stdio → Type
  #   @[extern "lean_io_process_spawn"] opaque spawn (args : SpawnArgs) : IO (Child args.toStdioConfig)
  #   @[extern "lean_io_process_child_wait"] opaque Child.wait {cfg : @& StdioConfig} : @& Child cfg → IO UInt32
  #   @[extern "lean_io_process_child_try_wait"] opaque Child.tryWait {cfg : @& StdioConfig} : @& Child cfg →
  #   @[extern "lean_io_process_child_kill"] opaque Child.kill {cfg : @& StdioConfig} : @& Child cfg → IO Unit
  #   @[extern "lean_io_process_child_take_stdin"] opaque Child.takeStdin {cfg : @& StdioConfig} : Child cfg →
  #   def output (args : SpawnArgs) (input? : Option String := none) : IO Output := do
  #   def run (args : SpawnArgs) (input? : Option String := none) : IO String := do
  #   @[extern "lean_io_exit"] opaque exit : UInt8 → IO α
  # end Process
  # def AccessRight.flags (acc : AccessRight) : UInt32 :=
  # def FileRight.flags (acc : FileRight) : UInt32 :=
  # @[extern "lean_chmod"] opaque Prim.setAccessRights (filename : @& FilePath) (mode : UInt32) : IO Unit
  # def setAccessRights (filename : FilePath) (mode : FileRight) : IO Unit :=
  abbrev Ref (α : Type) := ST.Ref IO.RealWorld α
  instance : MonadLift (ST IO.RealWorld) BaseIO := ⟨id⟩
  def mkRef (a : α) : BaseIO (IO.Ref α) :=

                # This is a more flexible alternative to `Task.cancel` as the token can be shared between multiple tasks.
  structure CancelToken where
    private ref : IO.Ref Bool
  namespace CancelToken
    def new : BaseIO CancelToken :=
    def set (tk : CancelToken) : BaseIO Unit :=
    def isSet (tk : CancelToken) : BaseIO Bool :=
  end CancelToken

  namespace FS
    # namespace Stream
    #   def ofHandle (h : Handle) : Stream where
          # structure Buffer where
          #   /-- The contents of the buffer. -/
          #   data : ByteArray := ByteArray.empty
          #   /-- The read/write cursor's position in the buffer. -/
          #   pos  : Nat := 0
    #   def ofBuffer (r : Ref Buffer) : Stream where
    #   partial def readBinToEndInto (s : Stream) (buf : ByteArray) : IO ByteArray := do
    #   def readBinToEnd (s : Stream) : IO ByteArray := do
    #   def readToEnd (s : Stream) : IO String := do
    #   partial def lines (s : Stream) : IO (Array String) := do
    # end Stream

    # def withIsolatedStreams [Monad m] [MonadFinally m] [MonadLiftT BaseIO m] (x : m α) (isolateStderr := true) : m (String × α) := do
  end FS
end IO
# @[extern "lean_runtime_mark_multi_threaded"] def Runtime.markMultiThreaded (a : α) : BaseIO α := return a
# @[extern "lean_runtime_mark_persistent"] unsafe def Runtime.markPersistent (a : α) : BaseIO α := return a
# @[extern "lean_runtime_forget"] def Runtime.forget (a : α) : BaseIO Unit := return
```

# src/Init/System/Promise.lean

```python
  # `Promise α` allows you to create a `Task α` whose value is provided later by calling `resolve`.
  #
  # Typical usage is as follows:
  # 1. `let promise ← Promise.new` creates a promise
  # 2. `promise.result? : Task (Option α)` can now be passed around
  # 3. `promise.result?.get` blocks until the promise is resolved
  # 4. `promise.resolve a` resolves the promise
  # 5. `promise.result?.get` now returns `some a`
  #
  # If the promise is dropped without ever being resolved, `promise.result?.get` will return `none`.
  #
  # See `Promise.result!/resultD` for other ways to handle this case.
def Promise (α : Type) : Type := PromiseImpl α
  @[extern "lean_io_promise_new"] opaque Promise.new [Nonempty α] : BaseIO (Promise α)
  @[extern "lean_io_promise_resolve"] opaque Promise.resolve (value : α) (promise : @& Promise α) : BaseIO Unit
  @[extern "lean_io_promise_result_opt"] opaque Promise.result? (promise : @& Promise α) : Task (Option α)
  def Promise.result! (promise : @& Promise α) : Task α :=
  def Promise.resultD (promise : Promise α) (dflt : α) : Task α :=
  def Promise.isResolved (promise : Promise α) : BaseIO Bool :=
```

# src/Std/Sync/Mutex.lean

```python
def BaseMutex : Type := BaseMutexImpl.type
instance : Nonempty BaseMutex := by exact BaseMutexImpl.property
@[extern "lean_io_basemutex_new"] opaque BaseMutex.new : BaseIO BaseMutex
@[extern "lean_io_basemutex_lock"] opaque BaseMutex.lock (mutex : @& BaseMutex) : BaseIO Unit
@[extern "lean_io_basemutex_try_lock"] opaque BaseMutex.tryLock (mutex : @& BaseMutex) : BaseIO Bool
@[extern "lean_io_basemutex_unlock"] opaque BaseMutex.unlock (mutex : @& BaseMutex) : BaseIO Unit
def Condvar : Type := CondvarImpl.type
instance : Nonempty Condvar := by exact CondvarImpl.property
@[extern "lean_io_condvar_new"] opaque Condvar.new : BaseIO Condvar # it is using std::condition_variable (check thread.cpp)
@[extern "lean_io_condvar_wait"] opaque Condvar.wait (condvar : @& Condvar) (mutex : @& BaseMutex) : BaseIO Unit # Waits until another thread calls `notifyOne` or `notifyAll`.
@[extern "lean_io_condvar_notify_one"] opaque Condvar.notifyOne (condvar : @& Condvar) : BaseIO Unit # Wakes up a single other thread executing `wait`.
@[extern "lean_io_condvar_notify_all"] opaque Condvar.notifyAll (condvar : @& Condvar) : BaseIO Unit # Wakes up all other threads executing `wait`.
def Condvar.waitUntil [Monad m] [MonadLiftT BaseIO m] (condvar : Condvar) (mutex : BaseMutex) (pred : m Bool) : m Unit := do # Waits on the condition variable until the predicate is true.

  structure Mutex (α : Type) where private mk ::
    private ref : IO.Ref α
    mutex : BaseMutex
    deriving Nonempty

instance : CoeOut (Mutex α) BaseMutex where coe := Mutex.mutex
def Mutex.new (a : α) : BaseIO (Mutex α) :=
  # `AtomicT α m` is the monad that can be atomically executed inside a `Mutex α`,
  # with outside monad `m`.
  # The action has access to the state `α` of the mutex (via `get` and `set`).
  abbrev AtomicT := StateRefT' IO.RealWorld
def Mutex.atomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m] (mutex : Mutex α) (k : AtomicT α m β) : m β := do
  # `mutex.atomically k` runs `k` with access to the mutex's state while locking the mutex.
def Mutex.tryAtomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m] (mutex : Mutex α) (k : AtomicT α m β) : m β := do
  # `mutex.atomicallyOnce condvar pred k` runs `k`,
  # waiting on `condvar` until `pred` returns true.
  # Both `k` and `pred` have access to the mutex's state.
def Mutex.atomicallyOnce [Monad m] [MonadLiftT BaseIO m] [MonadFinally m] (mutex : Mutex α) (condvar : Condvar) (pred : AtomicT α m Bool) (k : AtomicT α m β) : m β :=
```

# src/Std/Sync/Channel.lean

```purescript
instance : ToString Error where
instance : MonadLift (EIO Error) IO where
def CloseableChannel (α : Type) : Type := CloseableChannel.Flavors α
  def new              (capacity : Option Nat := none)                                                    : BaseIO (CloseableChannel α) := do
  def trySend          (ch : CloseableChannel α) (v : α)                                                  : BaseIO Bool :=
  def send             (ch : CloseableChannel α) (v : α)                                                  : BaseIO (Task (Except Error Unit)) :=
  def tryRecv          (ch : CloseableChannel α)                                                          : BaseIO (Option α) :=
  def recv             (ch : CloseableChannel α)                                                          : BaseIO (Task (Option α)) :=
  def recvSelector     (ch : CloseableChannel α)                                                          : Selector (Option α) :=
  partial def forAsync (f : α → BaseIO Unit) (ch : CloseableChannel α) (prio : Task.Priority := .default) : BaseIO (Task Unit) := do

  def close (ch : CloseableChannel α) : EIO Error Unit := -- !!!
  def isClosed (ch : CloseableChannel α) : BaseIO Bool := -- !!!

  def sync (ch : CloseableChannel α) : CloseableChannel.Sync α := ch
def CloseableChannel.Sync (α : Type) : Type := CloseableChannel α
  def new     (capacity : Option Nat := none) : BaseIO (Sync α) := CloseableChannel.new capacity
  def trySend (ch : Sync α) (v : α)           : BaseIO Bool := CloseableChannel.trySend ch v
  def send    (ch : Sync α) (v : α)           : EIO Error Unit := do
  def tryRecv (ch : Sync α)                   : BaseIO (Option α) := CloseableChannel.tryRecv ch
  def recv    (ch : Sync α)                   : BaseIO (Option α) := do

  def close (ch : Sync α) : EIO Error Unit := CloseableChannel.close ch
  def isClosed (ch : Sync α) : BaseIO Bool := CloseableChannel.isClosed ch

  instance [MonadLiftT BaseIO m] : ForIn m (Sync α) α where
structure Channel (α : Type) where -- just wrapper over Closable
  def new              (capacity : Option Nat := none)                                           : BaseIO (Channel α) := do
  def trySend          (ch : Channel α) (v : α)                                                  : BaseIO Bool := -- same
  def send             (ch : Channel α) (v : α)                                                  : BaseIO (Task Unit) := do -- !!! `send` internally uses unreachable!. Why? You cannot close it! No such func!
  def tryRecv          (ch : Channel α)                                                          : BaseIO (Option α) := -- same
  def recv             (ch : Channel α)                                                          : BaseIO (Task α) := do -- !!!!
  def recvSelector     (ch : Channel α)                                                          : Selector α := -- !!!!
  partial def forAsync (f : α → BaseIO Unit) (ch : Channel α) (prio : Task.Priority := .default) : BaseIO (Task Unit) := do -- same
@[expose] def Channel.Sync (α : Type) : Type := Channel α
instance : Nonempty (Channel.Sync α) :=
  def sync (ch : Channel α) : Channel.Sync α := ch
  def new (capacity : Option Nat := none) : BaseIO (Sync α) := Channel.new capacity
  def trySend (ch : Sync α) (v : α) : BaseIO Bool := Channel.trySend ch v
  def send (ch : Sync α) (v : α) : BaseIO Unit := do
  def tryRecv (ch : Sync α) : BaseIO (Option α) := Channel.tryRecv ch
  def recv (ch : Sync α) : BaseIO α := do
  instance [Inhabited α] [MonadLiftT BaseIO m] : ForIn m (Sync α) α where
```

# src/Std/Sync/Basic.lean

```purescript
abbrev AtomicT := StateRefT' IO.RealWorld
```

# src/Std/Sync/RecursiveMutex.lean

```purescript
def BaseRecursiveMutex : Type := RecursiveMutexImpl.type
instance : Nonempty BaseRecursiveMutex := by exact RecursiveMutexImpl.property
@[extern "lean_io_baserecmutex_new"] opaque BaseRecursiveMutex.new : BaseIO BaseRecursiveMutex
@[extern "lean_io_baserecmutex_lock"] opaque BaseRecursiveMutex.lock (mutex : @& BaseRecursiveMutex) : BaseIO Unit
@[extern "lean_io_baserecmutex_try_lock"] opaque BaseRecursiveMutex.tryLock (mutex : @& BaseRecursiveMutex) : BaseIO Bool
@[extern "lean_io_baserecmutex_unlock"] opaque BaseRecursiveMutex.unlock (mutex : @& BaseRecursiveMutex) : BaseIO Unit
instance : CoeOut (RecursiveMutex α) BaseRecursiveMutex where coe := RecursiveMutex.mutex
def RecursiveMutex.new (a : α) : BaseIO (RecursiveMutex α) :=
def RecursiveMutex.atomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
def RecursiveMutex.tryAtomically [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
```

# src/Std/Internal/Async/Basic.lean

```purescript
namespace Std
  namespace Internal
    namespace IO
      namespace Async
        class MonadAwait (t : Type → Type) (m : Type → Type) extends Monad m where
        class MonadAsync (t : Type → Type) (m : Type → Type) extends Monad m where
        instance [Monad m] [MonadAwait t m] : MonadAwait t (StateT n m) where
        instance [Monad m] [MonadAwait t m] : MonadAwait t (ExceptT n m) where
        instance [Monad m] [MonadAwait t m] : MonadAwait t (ReaderT n m) where
        instance [MonadAwait t m] : MonadAwait t (StateRefT' s n m) where
        instance [MonadAwait t m] : MonadAwait t (StateT s m) where
        instance [MonadAsync t m] : MonadAsync t (ReaderT n m) where
        instance [MonadAsync t m] : MonadAsync t (StateRefT' s n m) where
        instance [Functor t] [inst : MonadAsync t m] : MonadAsync t (StateT s m) where

        def background [Monad m] [MonadAsync t m] (prio := Task.Priority.default) : m α → m Unit :=
        def concurrently [Monad m] [MonadAwait t m] [MonadAsync t m] (x : m α) (y : m β) (prio := Task.Priority.default) : m (α × β) := do
        def race [MonadLiftT BaseIO m] [MonadAwait Task m] [MonadAsync t m] [MonadAwait t m] [Monad m] [Inhabited α] (x : m α) (y : m α) (prio := Task.Priority.default) : m α := do
        def concurrentlyAll
            [Monad m] [MonadAwait t m] [MonadAsync t m] (xs : Array (m α))
            (prio := Task.Priority.default) :
            m (Array α) := do
        def raceAll
            [ForM m c (m α)] [MonadLiftT BaseIO m] [MonadAwait Task m]
            [MonadAsync t m] [MonadAwait t m] [Monad m] [Inhabited α]
            (xs : c)
            (prio := Task.Priority.default) :
            m α := do

        abbrev ETask (ε : Type) (α : Type) : Type
          := ExceptT ε Task α
          := Task (Except ε α)
        namespace ETask
          protected def pure (x : α) : ETask ε α :=
          protected def map (f : α → β) (x : ETask ε α) (prio := Task.Priority.default) (sync := false) : ETask ε β :=
          protected def bind (x : ETask ε α) (f : α → ETask ε β) (prio := Task.Priority.default) (sync := false) : ETask ε β :=
          protected def bindEIO (x : ETask ε α) (f : α → EIO ε (ETask ε β)) (prio := Task.Priority.default) (sync := false) : EIO ε (ETask ε β) :=
          protected def mapEIO (f : α → EIO ε β) (x : ETask ε α) (prio := Task.Priority.default) (sync := false) : BaseIO (ETask ε β) :=
          def block (x : ETask ε α) : EIO ε α := do
          def ofPromise (x : IO.Promise (Except ε α)) : ETask ε α :=
          def ofPurePromise (x : IO.Promise α) : ETask ε α :=
          def getState (x : ETask ε α) : BaseIO IO.TaskState :=
          instance : Functor (ETask ε) where
          instance : Monad (ETask ε) where
        end ETask
        abbrev AsyncTask := ETask IO.Error = ExceptT IO.Error Task := Task (Except IO.Error α)
        namespace AsyncTask
          protected def mapIO (f : α → IO β) (x : AsyncTask α) (prio := Task.Priority.default) (sync := false) : BaseIO (AsyncTask β) :=
          protected def pure (x : α) : AsyncTask α :=
          protected def bind (x : AsyncTask α) (f : α → AsyncTask β) (prio := Task.Priority.default) (sync := false) : AsyncTask β :=
          def map (f : α → β) (x : AsyncTask α) (prio := Task.Priority.default) (sync := false) : AsyncTask β :=
          def bindIO (x : AsyncTask α) (f : α → IO (AsyncTask β)) (prio := Task.Priority.default) (sync := false) : BaseIO (AsyncTask β) :=
          def mapTaskIO (f : α → IO β) (x : AsyncTask α) (prio := Task.Priority.default) (sync := false) : BaseIO (AsyncTask β) :=
          def block (x : AsyncTask α) : IO α :=
          def ofPromise (x : IO.Promise (Except IO.Error α)) : AsyncTask α := -- Promise = AsyncTask
          def ofPurePromise (x : IO.Promise α) : AsyncTask α :=
          def getState (x : AsyncTask α) : BaseIO IO.TaskState :=
        end AsyncTask
        inductive MaybeTask (α : Type)
        namespace MaybeTask
          def toTask : MaybeTask α → Task α
          def get {α : Type} : MaybeTask α → α
          def map (f : α → β) (prio := Task.Priority.default) (sync := false) : MaybeTask α → MaybeTask β
          protected def bind (t : MaybeTask α) (f : α → MaybeTask β) (prio := Task.Priority.default) (sync := false) : MaybeTask β :=
          def joinTask (t : Task (MaybeTask α)) : Task α :=
          instance : Functor (MaybeTask) where
          instance : Monad (MaybeTask) where
        end MaybeTask
        def BaseAsync (α : Type)
          := BaseIO (MaybeTask α)
          := EIO Empty (MaybeTask α)
        namespace BaseAsync
          def mk (x : BaseIO (MaybeTask α)) : BaseAsync α :=
          def toRawBaseIO (x : BaseAsync α) : BaseIO (MaybeTask α) :=
          protected def toBaseIO (x : BaseAsync α) : BaseIO (Task α) :=
          protected def ofTask (x : Task α) : BaseAsync α :=
          protected def pure (a : α) : BaseAsync α :=
          protected def map (f : α → β) (self : BaseAsync α) (prio := Task.Priority.default) (sync := false) : BaseAsync β :=
          protected def bind (self : BaseAsync α) (f : α → BaseAsync β) (prio := Task.Priority.default) (sync := false) : BaseAsync β :=
          protected def lift (x : BaseIO α) : BaseAsync α :=
          protected def wait (self : BaseAsync α) : BaseIO α :=
          protected def asTask (x : BaseAsync α) (prio := Task.Priority.default) : BaseIO (Task α) := do -- lean_io_as_task does work
          def await (t : Task α) : BaseAsync α :=
          def async (self : BaseAsync α) (prio := Task.Priority.default) : BaseAsync (Task α) := -- EIO Empty (MaybeTask (Task α))
          instance : Functor BaseAsync where
          instance : Monad BaseAsync where
          instance : MonadLift BaseIO BaseAsync where
          instance : MonadAwait Task BaseAsync where
          instance : MonadAsync Task BaseAsync where
          instance [Inhabited α] : Inhabited (BaseAsync α) where
        end BaseAsync
        def EAsync (ε : Type) (α : Type)
            := BaseAsync (Except ε α)
            := BaseIO (MaybeTask (Except ε α))
            := EIO Empty (MaybeTask (Except ε α))
        namespace EAsync
          protected def toBaseIO (x : EAsync ε α) : BaseIO (ETask ε α) :=
          protected def ofTask (x : ETask ε α) : EAsync ε α :=
          protected def toEIO (x : EAsync ε α) : EIO ε (ETask ε α) :=
          protected def ofETask (x : ETask ε α) : EAsync ε α :=
          protected def pure (a : α) : EAsync ε α :=
          protected def map (f : α → β) (self : EAsync ε α) : EAsync ε β :=
          protected def bind (self : EAsync ε α) (f : α → EAsync ε β) : EAsync ε β :=
          protected def lift (x : EIO ε α) : EAsync ε α :=
          protected def wait (self : EAsync ε α) : EIO ε α := do
          protected def asTask (x : EAsync ε α) (prio := Task.Priority.default) : EIO ε (ETask ε α) :=
          protected def throw (e : ε) : EAsync ε α :=
          protected def tryCatch (x : EAsync ε α) (f : ε → EAsync ε α) (prio := Task.Priority.default) (sync := false) : EAsync ε α :=
          protected def tryFinally'
          def await (x : ETask ε α) : EAsync ε α :=
          def async (self : EAsync ε α) (prio := Task.Priority.default) : EAsync ε (ETask ε α) :=
          instance : Functor (EAsync ε) where
          instance : Monad (EAsync ε) where
          instance : MonadLift (EIO ε) (EAsync ε) where
          instance : MonadExcept ε (EAsync ε) where
          instance : MonadExceptOf ε (EAsync ε) where
          instance : MonadFinally (EAsync ε) where
          instance : OrElse (EAsync ε α) where
          instance [Inhabited ε] : Inhabited (EAsync ε α) where
          instance : MonadAwait (ETask ε) (EAsync ε) where
          instance : MonadAwait Task (EAsync ε) where
          instance : MonadAwait AsyncTask (EAsync IO.Error) where
          instance : MonadAwait IO.Promise (EAsync ε) where
          instance : MonadAsync (ETask ε) (EAsync ε) where
          instance : MonadAsync AsyncTask (EAsync IO.Error) where
          instance : MonadLift BaseIO (EAsync ε) where
          instance : MonadLift (EIO ε) (EAsync ε) where
          instance : MonadLift BaseAsync (EAsync ε) where
          protected partial def forIn
          instance [Inhabited ε] : ForIn (EAsync ε) Lean.Loop Unit where
        end EAsync
        abbrev Async (α : Type)
          := EAsync IO.Error α
          := BaseAsync (Except IO.Error α)
          := BaseIO (MaybeTask (Except IO.Error α))
          := EIO Empty (MaybeTask (Except IO.Error α))
          -- := EStateM Empty IO.RealWorld (MaybeTask (Except IO.Error α))
          -- := IO.RealWorld → Result Empty IO.RealWorld (MaybeTask (Except IO.Error α))
          -- := Unit → MaybeTask (Except IO.Error α)
        namespace Async
          protected def toIO (x : Async α) : IO (AsyncTask α) := -- IO (Task (Except IO.Error α))
          instance : MonadAsync AsyncTask Async :=
          instance : MonadAwait AsyncTask Async :=
          instance : MonadAwait IO.Promise Async :=
        end Async
      end Async
    end IO
  end Internal
end Std
```

src/Std/Internal/Async/Timer.lean

```python
namespace Std
  namespace Internal
    namespace IO
      namespace Async
        structure Sleep where
          private ofNative ::
            native : Internal.UV.Timer # just a wrapper, internal tests async_sleep.lean, wrapper tests async_surface_sleep.lean

        namespace Sleep
          def mk (duration : Std.Time.Millisecond.Offset) : IO Sleep := # doesnt start
          def reset (s : Sleep) : IO Unit := # reset if running
          def stop (s : Sleep) : IO Unit := # will make AsyncTask run forever
          def wait (s : Sleep) : IO (AsyncTask Unit) := # starts
          def selector (s : Sleep) : IO (Selector Unit) := # starts too, bc uses wait
        end Sleep

        def sleep (duration : Std.Time.Millisecond.Offset) : IO (AsyncTask Unit) := # mk + wait
        def Selector.sleep (duration : Std.Time.Millisecond.Offset) : IO (Selector Unit) := # mk + selector

        structure Interval where
          private ofNative ::
            native : Internal.UV.Timer
        namespace Interval
          def mk (duration : Std.Time.Millisecond.Offset) (_ : 0 < duration := by decide) : IO Interval :=
          def tick (i : Interval) : IO (AsyncTask Unit) :=
          def reset (i : Interval) : IO Unit :=
          def stop (i : Interval) : IO Unit :=
        end Interval
      end Async
    end IO
  end Internal
end Std
```

# src/Std/Internal/Async/Select.lean

```purescript
public import Std.Internal.Async.Basic

namespace Std
  namespace Internal
    namespace IO
      namespace Async
        structure Waiter (α : Type) where
          private mk ::
            private finished : IO.Ref Bool
            promise : IO.Promise (Except IO.Error α)
        def Waiter.withPromise (w : Waiter α) (p : IO.Promise (Except IO.Error β)) : Waiter β := -- wait one, wait second
        def Waiter.race [Monad m] [MonadLiftT (ST IO.RealWorld) m] (w : Waiter α) (lose : m β) (win : IO.Promise (Except IO.Error α) → m β) : m β := do -- more apt is `loose` or `markAsLooser w actionIfRnNotFinished actionIfRnFinished`
        def Waiter.checkFinished [Monad m] [MonadLiftT (ST IO.RealWorld) m] (w : Waiter α) : m Bool := do
        structure Selector (α : Type) where
          tryFn : IO (Option α)
          registerFn : Waiter α → IO Unit
          unregisterFn : IO Unit
        structure Selectable (α : Type) where
          case :: {β : Type}
            selector : Selector β
            cont : β → IO (AsyncTask α)
        partial def Selectable.one (selectables : Array (Selectable α)) : IO (AsyncTask α) := do
      end Async
    end IO
  end Internal
end Std
```
