Security requirements
---------------------

Multiple security considerations have been taken into account at design time.
These considerations are the consequence of a security study with respect for
the core usage of the Outpost OS and the Sentry kernel, which targets small embedded
systems.

The consideration are the following:

   1. As much as possible properties must be a build-time information that can be
      verified before flashing the target. To achieve that, Sentry kernel consider
      a lot of information as being build-time produced. This includes:

      * the task list ()

   1.
