# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

*** Settings ***

Documentation   Sentry Kernel boot report generation
...             Boot kernel, and check that execution reach the start task step

Library         SerialLibrary
Library         String
Library         DependencyLibrary
Library         PyocdLibrary

*** Variables ***

${PROMPT}          [AT]
${SOCLINE}             _entrypoint: booting on SoC

*** Test Cases ***

Load Autotest
    [Documentation]         Read autotest content from serial line

    Reset

    Load Firmware           builddir/firmware.hex
    Open Serial Port
    Read All
    Resume

    ${read_all}             Read Until  terminator=mgr_task_start: spawning thread
    Close Serial Port
    Should Contain          ${read_all}    mgr_task_start: spawning thread
    ${SoC_Line}             Get Lines Containing String     ${read_all}      _entrypoint: booting on SoC
    ${SoC}                  Fetch From Right    ${SoC_Line}     ${SPACE}
    Log   ${read_all}
    Set Test Message        Autotest executed on SoC ${SoC}

*** Keywords ***

Open Serial Port
    Connect        /dev/ttyACM0    115200
    Set Timeout    5

Close Serial Port
    Disconnect
