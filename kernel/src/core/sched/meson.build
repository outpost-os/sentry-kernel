# schedulers implementations
sentry_sched_fifo_c = files(
    'sched_fifo.c',
)
sentry_sched_rrmq_c = files(
    'sched_rrmq.c',
)

sentry_source_set.add(when: 'CONFIG_SCHED_FIFO', if_true: sentry_sched_fifo_c)
sentry_source_set.add(when: 'CONFIG_SCHED_RRMQ', if_true: sentry_sched_rrmq_c)
