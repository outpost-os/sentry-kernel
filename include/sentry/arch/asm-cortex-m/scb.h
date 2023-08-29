#ifndef SCB_H
#define SCB_H

#include <ktypes.h>
#include "system.h"

/* SCB Registers */
#define r_CORTEX_M_SCB_ACTLR                REG_ADDR(SCS_BASE + 0x08u)    /* (R/W)  Auxiliary control register */

#define r_CORTEX_M_SCB				        REG_ADDR(SCB_BASE + 0x00u)
#define r_CORTEX_M_SCB_CPUID                REG_ADDR(SCB_BASE + 0x00u)    /* (R/ )  CPUID Base Register */
#define r_CORTEX_M_SCB_ICSR                 REG_ADDR(SCB_BASE + 0x04u)    /* (R/W)  Interrupt Control and State Register */
#define r_CORTEX_M_SCB_VTOR                 REG_ADDR(SCB_BASE + 0x08u)    /* (R/W)  Vector Table Offset Register */
#define r_CORTEX_M_SCB_AIRCR                REG_ADDR(SCB_BASE + 0x0Cu)    /* (R/W)  Application Interrupt and Reset Control Register */
#define r_CORTEX_M_SCB_SCR                  REG_ADDR(SCB_BASE + 0x10u)    /* (R/W)  System Control Register */
#define r_CORTEX_M_SCB_CCR                  REG_ADDR(SCB_BASE + 0x14u)    /* (R/W)  Configuration Control Register */

#define r_CORTEX_M_SCB_SHPR1                REG_ADDR(SCB_BASE + 0x18u)    /* (R/W)  System Handlers Priority Registers (4-6) */
#define r_CORTEX_M_SCB_SHPR2                REG_ADDR(SCB_BASE + 0x1Cu)    /* (R/W)  System Handlers Priority Registers (11) */
#define r_CORTEX_M_SCB_SHPR3                REG_ADDR(SCB_BASE + 0x20u)    /* (R/W)  System Handlers Priority Registers (14-15) */

#define r_CORTEX_M_SCB_SHCSR                REG_ADDR(SCB_BASE + 0x24u)    /* (R/W)  System Handler Control and State Register */

#define r_CORTEX_M_SCB_CFSR                 REG_ADDR(SCB_BASE + 0x28u)    /* (R/W)  Configurable Fault Status Register  */
#define r_CORTEX_M_SCB_MMSR                 REG_ADDR(SCB_BASE + 0x28u)    /* (R/W)  MemManage Fault Address Register (A subregister of the CFSR) */
#define r_CORTEX_M_SCB_BFSR                 REG_ADDR(SCB_BASE + 0x29u)    /* (R/W)  BusFault Status Register  */
#define r_CORTEX_M_SCB_UFSR                 REG_ADDR(SCB_BASE + 0x2au)    /* (R/W)  UsageFault Status Register  */

#define r_CORTEX_M_SCB_HFSR                 REG_ADDR(SCB_BASE + 0x2cu)    /* (R/W)  Hard fault status register  */
#define r_CORTEX_M_SCB_MMAR                REG_ADDR(SCB_BASE + 0x34u)    /* (R/W)  Memory management fault address register */
#define r_CORTEX_M_SCB_BFAR                 REG_ADDR(SCB_BASE + 0x38u)    /* (R/W)  Bus fault address register (BFAR) */
#define r_CORTEX_M_SCB_AFSR                 REG_ADDR(SCB_BASE + 0x3cu)    /* (R/W)  Auxiliary fault status register */

#define r_CORTEX_M_SCB_CPACR                REG_ADDR(SCB_BASE + 0x88u)    /* (R/W)  Coprocessor Access Control register */

/* Auxiliary control register Définitions */
#define SCB_ACTLR_DISOOFP_Pos               9u   /* Bit 9 DISOOFP  */
#define SCB_ACTLR_DISOOFP_Msk               (0x01u << SCB_ACTLR_DISOOFP_Pos)
#define SCB_ACTLR_DISFPCA_Pos               8u   /* Bit 8 DISFPCA  */
#define SCB_ACTLR_DISFPCA_Msk               (0x01u << SCB_ACTLR_DISFPCA_Pos)
#define SCB_ACTLR_DISFOLD_Pos               2u   /* Bit 2 DISFOLD  */
#define SCB_ACTLR_DISFOLD_Msk               (0x01u << SCB_ACTLR_DISFOLD_Pos)
#define SCB_ACTLR_DISDEFWBUF_Pos            1u   /* Bit 1 DISDEFWBUF   */
#define SCB_ACTLR_DISDEFWBUF_Msk            (0x01u << SCB_ACTLR_DISDEFWBUF_Pos)
#define SCB_ACTLR_DISMCYCINT_Pos            0u   /* Bit 0 DISMCYCINT   */
#define SCB_ACTLR_DISMCYCINT_Msk            (0x01u << SCB_ACTLR_DISMCYCINT_Pos)

/* SCB Application Interrupt and Reset Control Register Definitions */
#define SCB_AIRCR_ENDIANNESS_Pos           15u   /* Bit 15 ENDIANNESS Data endianness bit */
#define SCB_AIRCR_ENDIANNESS_Msk           (0x01u << SCB_AIRCR_ENDIANNESS_Pos)


//System handler priority register 1 (SHPR1)
#define SCB_SHPR1_PRI_4_Pos                 0u   /* Bits 7:0 PRI_4:
                                                   Priority of system handler 4,
                                                   memory management fault */
#define SCB_SHPR1_PRI_4_Msk                 (0xffu << SCB_SHPR1_PRI_4_Pos)

#define SCB_SHPR1_PRI_5_Pos                 8u   /* Bits 15:8 PRI_5:
                                                   Priority of system handler 5, bus fault */
#define SCB_SHPR1_PRI_5_Msk                 (0xffu << SCB_SHPR1_PRI_5_Pos)

//System handler priority register 2 (SHPR2)
#define SCB_SHPR2_PRI_6_Pos                 16u  /* Bits 23:16 PRI_6:
                                                   Priority of system handler 6, usage fault */
#define SCB_SHPR2_PRI_6_Msk                 (0xffu << SCB_SHPR2_PRI_6_Pos)
#define SCB_SHPR2_PRI_11_Pos                 24u /* Bits 31:24 PRI_11:
                                                   Priority of system handler 11, SVCall */
#define SCB_SHPR2_PRI_11_Msk                (0xffu << SCB_SHPR2_PRI_11_Pos)

//System handler priority register 3 (SHPR3)
#define SCB_SHPR3_PRI_14_Pos                16u  /* Bits 23:16 PRI_14:
                                                   Priority of system handler 14, PendSV */
#define SCB_SHPR3_PRI_14_Msk                (0xffu << SCB_SHPR3_PRI_14_Pos)
#define SCB_SHPR3_PRI_15_Pos                24u  /* Bits 31:24 PRI_15:
                                                   Priority of system handler 15, SysTick exception */
#define SCB_SHPR3_PRI_15_Msk                (0xffu << SCB_SHPR3_PRI_15_Pos)

/* Configurable fault status register (CFSR; UFSR+BFSR+MMFSR)
 * The CFSR is byte accessible. You can access the CFSR or its subregisters as follows:
 * • Access the complete CFSR with a word access to 0xE000ED28
 * • Access the MMFSR with a byte access to 0xE000ED28
 * • Access the MMFSR and BFSR with a halfword access to 0xE000ED28
 * • Access the BFSR with a byte access to 0xE000ED29
 * • Access the UFSR with a halfword access to 0xE000ED2A.
 *
 * The CFSR indicates the cause of a memory management fault, bus fault, or usage fault.
 */

#define SCB_CFSR_UFSR_Pos                       16u  /* Bits 31:16 UFSR:
                                                       Usage fault status register (UFSR) */
#define SCB_CFSR_UFSR_Msk                       (0xffffu << SCB_CFSR_UFSR_Pos)
#define SCB_CFSR_BFSR_Pos                       8u   /* Bits 15:8 BFSR:
                                                       Bus fault status register (BFSR) */
#define SCB_CFSR_BFSR_Msk                       (0xffu << SCB_CFSR_BFSR_Pos)
#define SCB_CFSR_MMFSR_Pos                      0u   /* Bits 7:0 MMFSR:
                                                       Memory management fault address register (MMFSR) */
#define SCB_CFSR_MMFSR_Msk                      (0xffu << SCB_CFSR_MMFSR_Pos)

 /* Usage fault status register (UFSR) */
#define SCB_CFSR_UFSR_DIVBYZERO_Pos              25u /* Bit 25 DIVBYZERO:
                                                       Divide by zero usage fault. */
#define SCB_CFSR_UFSR_DIVBYZERO_Msk              (0x01u << SCB_UFSR_DIVBYZERO_Pos)
#define SCB_CFSR_UFSR_UNALIGNED_Pos              24u /* Bit 24 UNALIGNED:
                                                       Unaligned access usage fault. */
#define SCB_CFSR_UFSR_UNALIGNED_Msk              (0x01u << SCB_UFSR_UNALIGNED_Pos)
#define SCB_CFSR_UFSR_NOCP_Pos                   19u /* Bit 19 NOCP:
                                                       No coprocessor usage fault. */
#define SCB_CFSR_UFSR_NOCP_Msk                   (0x01u << SCB_UFSR_NOCP_Pos)
#define SCB_CFSR_UFSR_INVPC_Pos                  18u /* Bit 18 INVPC:
                                                       Invalid PC load usage fault,
                                                       caused by an invalid PC load by EXC_RETURN */
#define SCB_CFSR_UFSR_INVPC_Msk                  (0x01u << SCB_UFSR_INVPC_Pos)
#define SCB_CFSR_UFSR_INVSTATE_Pos               17u /* Bit 17 INVSTATE:
                                                       Invalid state usage fault. */
#define SCB_CFSR_UFSR_INVSTATE_Msk               (0x01u << SCB_UFSR_INVSTATE_Pos)
#define SCB_CFSR_UFSR_UNDEFINSTR_Pos             16u /* Bit 16 UNDEFINSTR:
                                                       Undefined instruction usage fault. */
#define SCB_CFSR_UFSR_UNDEFINSTR_Msk             (0x01u << SCB_UFSR_UNDEFINSTR_Pos)

/* Bus fault status register (BFSR) */
#define SCB_CFSR_BFSR_BFARVALID_Pos              15u /* Bit 15 BFARVALID:
                                                       Bus Fault Address Register (BFAR) valid flag.
                                                       The processor sets this bit to 1 */
#define SCB_CFSR_BFSR_BFARVALID_Msk              (0x01u << SCB_BFSR_BFARVALID_Pos)
#define SCB_CFSR_BFSR_LSPERR_Pos                 13u /* Bit 13 LSPERR:
                                                       Bus fault on floating-point lazy state preservation. */
#define SCB_CFSR_BFSR_LSPERR_Msk                 (0x01u << SCB_BFSR_LSPERR_Pos)
#define SCB_CFSR_BFSR_STKERR_Pos                 12u /* Bit 12 STKERR:
                                                       Bus fault on stacking for exception entry. */
#define SCB_CFSR_BFSR_STKERR_Msk                 (0x01u << SCB_BFSR_STKERR_Pos)
#define SCB_CFSR_BFSR_UNSTKERR_Pos               11u /* Bit 11 UNSTKERR:
                                                       Bus fault on unstacking for a return from exception. */
#define SCB_CFSR_BFSR_UNSTKERR_Msk               (0x01u << SCB_BFSR_UNSTKERR_Pos)
#define SCB_CFSR_BFSR_IMPRECISERR_Pos            10u /* Bit 10 IMPRECISERR:
                                                       Imprecise data bus error. */
#define SCB_CFSR_BFSR_IMPRECISERR_Msk            (0x01u << SCB_BFSR_IMPRECISERR_Pos)
#define SCB_CFSR_BFSR_PRECISERR_Pos              9u  /* Bit 9 PRECISERR:
                                                       Precise data bus error. */
#define SCB_CFSR_BFSR_PRECISERR_Msk              (0x01u << SCB_BFSR_PRECISERR_Pos)
#define SCB_CFSR_BFSR_IBUSERR_Pos                8u  /* Bit 8 IBUSERR:
                                                       Instruction bus error. */
#define SCB_CFSR_BFSR_IBUSERR_Msk                (0x01u << SCB_BFSR_IBUSERR_Pos)

/* Memory management fault address register (MMFSR)*/
#define SCB_CFSR_MMFSR_MMARVALID_Pos             7u  /* Bit 7 MMARVALID:
                                                       Memory Management Fault Address Register (MMAR) valid flag. */
#define SCB_CFSR_MMFSR_MMARVALID_Msk             (0x01u << SCB_CFSR_MMFSR_MMARVALID_Pos)
#define SCB_CFSR_MMFSR_MLSPERR_Pos               5u  /* Bit 5 MLSPERR:
                                                       MemManage fault  status */
#define SCB_CFSR_MMFSR_MLSPERR_Msk               (0x01u << SCB_CFSR_MMFSR_MLSPERR_Pos)
#define SCB_CFSR_MMFSR_MSTKERR_Pos               4u  /* Bit 4 MSTKERR:
                                                       Memory manager fault on stacking for exception entry. */
#define SCB_CFSR_MMFSR_MSTKERR_Msk               (0x01u << SCB_CFSR_MMFSR_MSTKERR_Pos)
#define SCB_CFSR_MMFSR_MUNSTKERR_Pos             3u  /* Bit 3 MUNSTKERR:
                                                       Memory manager fault on unstacking
                                                       for a return from exception. */
#define SCB_CFSR_MMFSR_MUNSTKERR_Msk             (0x01u << SCB_CFSR_MMFSR_MUNSTKERR_Pos)
#define SCB_CFSR_MMFSR_DACCVIOL_Pos              1u  /* Bit 1 DACCVIOL:
                                                       Data access violation flag. */
#define SCB_CFSR_MMFSR_DACCVIOL_Msk              (0x01u << SCB_CFSR_MMFSR_DACCVIOL_Pos)

#define SCB_CFSR_MMFSR_IACCVIOL_Pos              0u  /* Bit 0 IACCVIOL:
                                                       Instruction access violation flag.
                                                       This fault occurs on any access to an XN region */
#define SCB_CFSR_MMFSR_IACCVIOL_Msk              (0x01u << SCB_CFSR_MMFSR_Pos)

/* Hard fault status register (HFSR)*/
#define SCB_HFSR_DEBUG_VT_Pos                   31u  /*  Bit 31 DEBUG_VT:
                                                       Reserved for Debug use.
                                                       When writing to the register you must write 0 to this bit */
#define SCB_HFSR_DEBUG_VT_Msk              (0x01u << SCB_HFSR_DEBUG_VT_Pos)

/* Memory management fault address register (MMFAR) */
#define SCB_MMFAR_Pos                       0u   /* Bits 31:0 MMFAR: Memory management fault address */
#define SCB_MMFAR_Msk                       (0xffffffffu << SCB_MMFAR_Pos)

/* Bus fault address register (BFAR) */
#define SCB_BFAR_Pos                        0u   /* Bits 31:0 Bus fault address
                                                   When the BFARVALID bit of the BFSR is set to 1,
                                                   this field holds the address f the location that
                                                   generated the bus fault. When an unaligned access faults
                                                   the address in the BFAR is the one requested by the instruction,
                                                   even if it is not the address of the fault. */
#define SCB_BFAR_Msk                        (0xffffffffu << SCB_BFAR_Pos)

/* Auxiliary fault status register (AFSR) */
#define SCB_AFSR_IMPDEF_Pos                  0u  /* Bits 31:0 IMPDEF:
                                                   Implementation defined.
                                                   The AFSR contains additional system fault information. */
#define SCB_AFSR_IMPDEF_Msk                  (0xffffffffu << SCB_AFSR_IMPDEF_Pos)

#endif/*!SCB_H*/
