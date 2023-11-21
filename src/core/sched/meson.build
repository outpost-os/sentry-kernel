sentry_sched_fifo_c = files(
    'fifo.c',
)
sentry_sched_rrmq_c = files(
    'rrmq.c'
)

sentry_source_set.add(when: 'CONFIG_SCHED_FIFO', if_true: sentry_sched_fifo_c)
sentry_source_set.add(when: 'CONFIG_SCHED_RRMQ', if_true: sentry_sched_rrmq_c)
