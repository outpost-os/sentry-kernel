sys_pm_clock_set
""""""""""""""""

**API definition**

   .. code-block:: rust
      :caption: Rust UAPI for pm_clock_gate syscall

      mod uapi {
         fn pm_clock_set(clk_reg_offset: u32, clk_reg_value: u32) -> Status
      }

   .. code-block:: c
      :caption: C UAPI for pm_clock_set syscall

      enum Status sys_pm_clock_set(uint32_t reg_offset, uint32_t reg_value);

**Usage**

   Set a given RCC clock register to a given value. This syscall is required only
   in specific devices usage such as MIPI-DSI bridges, that require successive
   consecutive input PLL configuration.

**Required capability**

   CAPA_SYS_POWER is required as this impact the overall system power configuration.

**Return Values**

   * STATUS_DENIED if the calling task do not hold the CAPA_SYS_POWER capability
   * STATUS_INVALID if the given register offset is not supported for reconfiguration
   * STATUS_OK if the power configuration update is made properly
