ENTRY(Reset_Handler)

STACK_SIZE = DEFINED(__stack_size__) ? __stack_size__ : 0x0c00;

MEMORY
{
  INTERRUPTS (rx) : ORIGIN = 0x08000000, LENGTH = 0x00000400
  /* flash is ITCM, 128K */
  TEXT       (rx) : ORIGIN = 0x08000400, LENGTH = 0x0001FC00
  /* RAM is DTCM, 128K, 2 banks */
  RAM        (rw) : ORIGIN = 0x20000000, LENGTH = 0x00020000
}

_idlestack = _m7fw_init_psp_stack;

/* Define output sections */
SECTIONS
{
  /* The startup code goes first into FLASH */
  .isr_vector :
  {
    KEEP(*(.isr_vector)) /* Startup code */
    . = ALIGN(4);
  }>INTERRUPTS

  .task_list :
  {
    _task_list = .;
    *(.task_list)
    . = ALIGN(4);
    /*
      hold all the task static metadata (signed, versioned). Can be upgraded alone.
      Can be empty at kernel ELF generation (using _task_list pointer in code), but
      must be fullfill by build system when tasks positioned, based on kernel ELF
      to be pushed to dedicated memory slot instead, not TEXT
    */
  }>TEXT

  /* The program code and other data goes into FLASH */
  .text :
  {
    . = ALIGN(4);
    _stext = .;	            /* create a global symbol at data start */
    *startup*(.text.Reset_Handler)
    *(.text)
    *(.text*)
    *(.rodata)         	/* .rodata sections (constants, strings, etc.) */
    *(.rodata*)         	/* .rodata sections (constants, strings, etc.) */
    *(.glue_7)         	/* glue arm to thumb code */
    *(.glue_7t)        	/* glue thumb to arm code */
	*(.eh_frame)

    KEEP (*(.init))
    KEEP (*(.fini))

    . = ALIGN(4);
    _etext = .;        	/* define a global symbols at end of code */
    _exit = .;

    _sigot = .;

  }>TEXT

  .ARM.extab :
  {
    *(.ARM.extab* .gnu.linkonce.armextab.*)
  } > TEXT

  .ARM :
  {
    __exidx_start = .;
    *(.ARM.exidx*)
    __exidx_end = .;
  } > TEXT

 .ctors :
  {
    __CTOR_LIST__ = .;
    /* gcc uses crtbegin.o to find the start of
       the constructors, so we make sure it is
       first.  Because this is a wildcard, it
       doesn't matter if the user does not
       actually link against crtbegin.o; the
       linker won't look for a file to match a
       wildcard.  The wildcard also means that it
       doesn't matter which directory crtbegin.o
       is in.  */
    KEEP (*crtbegin.o(.ctors))
    KEEP (*crtbegin?.o(.ctors))
    /* We don't want to include the .ctor section from
       from the crtend.o file until after the sorted ctors.
       The .ctor section from the crtend file contains the
       end of ctors marker and it must be last */
    KEEP (*(EXCLUDE_FILE(*crtend?.o *crtend.o) .ctors))
    KEEP (*(SORT(.ctors.*)))
    KEEP (*(.ctors))
    __CTOR_END__ = .;
  } > TEXT

  .dtors :
  {
    __DTOR_LIST__ = .;
    KEEP (*crtbegin.o(.dtors))
    KEEP (*crtbegin?.o(.dtors))
    KEEP (*(EXCLUDE_FILE(*crtend?.o *crtend.o) .dtors))
    KEEP (*(SORT(.dtors.*)))
    KEEP (*(.dtors))
    __DTOR_END__ = .;
  } > TEXT

  /* used by the startup to initialize got */
  .got : AT ( _sigot ) {
    . = ALIGN(4);
        _sgot = .;
        /*  *(.got.plt)
         *    We don't need plt segment
         *    since we do not need dynamic library relocation
         */
        *(.got)
        *(.got*)
    . = ALIGN(4);
    _egot = .;

  /* used by the startup to initialize data */
    _sidata = .;
  }>TEXT

  __etext = .;    /* define a global symbol at end of code */
  __DATA_ROM = .; /* Symbol is used by startup for data initialization */



  /* used by the startup to initialize data */
  /* Initialized data sections goes into RAM, load LMA copy after code */
  .data : AT ( _sidata )
  {
    . = ALIGN(4);
    _ram_start = .;
    _sdata = .;        /* create a global symbol at data start */
    *(.data)           /* .data sections */
    *(.data*)          /* .data* sections */
    _edata = .;        /* define a global symbol at data end */
  }>RAM

  __CACHE_REGION_START = ORIGIN(INTERRUPTS);
  __CACHE_REGION_SIZE  = 0;
  __NDATA_ROM = __DATA_ROM + SIZEOF(.data); /* Symbol is used by startup for ncache data initialization */


  /* Uninitialized data section */
  . = ALIGN(4);
  .bss :
  {
    /* This is used by the startup in order to initialize the .bss section */
    _sbss = .;         /* define a global symbol at bss start */
    __bss_start__ = _sbss;
    *debug.o(.bss)
    *(.bss)
    *(.bss*)
    *(COMMON)

    . = ALIGN(4);
    _ebss = .;         /* define a global symbol at bss end */
    __bss_end__ = _ebss;
  }>RAM

    /* heap_stack section, used to check that there is enough RAM left */
  ._heap_stack :
  {
    . = ALIGN(4);
    PROVIDE ( end = . );
    PROVIDE ( _end = . );
    . = . + 2048;
    _idlestack = .;
    _estack = .;
    . = . + 4096;
    _m7fw_init_psp_stack = .;
    . = ALIGN(4);
  }>RAM


  /* Remove information from the standard libraries */
  /DISCARD/ :
  {
    libgcc.a ( * )
  }

}
