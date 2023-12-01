
mgr_device_files = files(
    'device.c',
)

sentry_source_set.add(mgr_device_files)

devices_template_h = files(['devlist-dt.h.in'])
devices_dtsgen_h = dtsgen.process(devices_template_h)
sentry_private_gen_header_set.add(devices_dtsgen_h)
