sys_send_ipc
""""""""""""
.. _uapi_send_ipc:

**API definition**

   .. code-block:: rust
       :caption: Rust UAPI for send_ipc syscall

       mod uapi {
           fn send_ipc(target: taskh_t, len: u32) -> Status
       }

   .. code-block:: c
       :caption: C UAPI for send_ipc syscall

       enum Status sys_send_ipc(taskh_t target, uint32_t len);

**Usage**

   Sending an Inter-Process Communication message toward the target job
   identified by the handle `taskh_t`.

   IPC are peace of data that are emitted between task's jobs. The data content
   type is not considered at kernel level, allowing jobs to emit any type of content,
   while short enough to be transmitted between `svc echange` zones.

   Emitting an IPC is always a blocking event. The job is preempted and is awakened
   only when:

      * the IPC target job read the IPC content
      * the IPC target job exists without reading the IPC (whatever the cause)

   IPC kernel implementation is a one-copy mechanism implementation. The effective
   IPC data copy is **not** done at send time but instead at **receive** time, by the
   target (see sys_recv_event for more information).

   Sentry IPC support direct and indirect deadlock detection, and thus allows to
   avoid any potential cycles that may generate user-space communication automaton
   locks. This is done by checking IPC cycles between tasks each time an IPC send
   syscall is executed.

   IPC do not require specific capability, but use task handles as target, requiring
   each task to know the target task label identifier before communicating.

   .. warning::
       IPC between tasks of different domains is forbidden


   The way IPC are executed use the following pseudocode (Ada-based pseudo-code):

   .. code-block:: ada

       procedure send_ipc
           (length: in u32; target: in taskh_t)
       is
       begin
           -- check IPC syscall inputs
           if length not in 1 .. MAX_IPC_LEN then
               current.syscall_return_value := ERROR_INVAL;
               return;
           end if;
           if job_do_not_exist(target) = TRUE then
               current.syscall_return_value := ERROR_NOENT;
               return;
           end if;

           -- check for direct or indirect deadlocks
           if ensure_no_deadlock(target, current) = FALSE then
               current.syscall_return_value := ERROR_DEADLOCK;
               return;
           end if;

           -- flag target IPC input that current task has emit an IPC. Non-zero is a trigger
           target.ipcs(current).length := len;

           -- awake target, if possible
           if awakable_for_ipc(target) then
               awake(target);
           end if;

           -- set current task job as unschedulable
           current.state := STATE_WAITFORIPC;

           -- elect a new job
           sched_elect;
           -- preemption here, until asynchronous event rise:
           -- - target read the IPC (valid awakening, no error)
           -- - target exit before IPC is read (invalid awakening: ERROR_BROKENPIPE)
       end send_ipc;

   .. note::
       If reaching the elect line, the syscall return value is asynchronously updated
       at handler level, before moving back to userspace, using the current.syscall_return_value

   .. note::
      IPCs are considered as a slow path. For high performance exchanges, use
      signals or shared memories

**Return values**

    STATUS_OKAY: IPC has been emitted and received (read) by peer.
    STATUS_INVALID: The IPC arguments are not valid.
    STATUS_DEADLK: emitting this IPC would generate an inter-task deadlock. Please check your own input IPC before emitting one.
