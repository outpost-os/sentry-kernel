# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

*** Settings ***

Documentation   Sentry Kernel boot report generation
...             Boot kernel, and check that execution reach the start task step

Library         SerialLibrary
Library         String
Library         DependencyLibrary
Library         PyocdLibrary    ${PROBE_UID}

*** Variables ***

${PROMPT}          [AT]
${SOCLINE}             _entrypoint: booting on SoC

*** Test Cases ***

Load Firmware
    [Documentation]         Read boot log content from serial line

    Should Not Be Empty     ${FIRMWARE_FILE}
    Reset
    Load Firmware           ${FIRMWARE_FILE}
    ${vcp}                  Get Probe Vcp
    Log                     Virtual port is ${vcp}
    Open Serial Port        ${vcp}
    Read All
    Resume
    ${read_all}             Read Until  terminator=mgr_task_start: spawning thread
    Close Serial Port
    Set Suite Variable      ${ALL_LOG}  ${read_all}

Target Metadata
    Should Contain          ${ALL_LOG}    mgr_task_start: spawning thread
    ${SoC_Line}             Get Lines Containing String     ${ALL_LOG}      _entrypoint: booting on SoC
    ${SoC}                  Fetch From Right    ${SoC_Line}     ${SPACE}
    ${Dts_Line}             Get Lines Containing String     ${ALL_LOG}      _entrypoint: configured dts file
    ${Dts}                  Fetch From Right    ${Dts_Line}     ${SPACE}
    Log   ${ALL_LOG}
    Set Test Message        firmware: boot on  SoC ${SoC} with DTS: ${Dts}

Check Complete Kernel Bootup
    Should Contain          ${ALL_LOG}    mgr_task_start: spawning thread

Fault Detection
    [Documentation]         Check if a fault is triggered

    Depends on test         Load Autotest
    ${handler}              Get Lines Containing String	${ALL_LOG}	fault_handler
    ${frame}                Get Lines Containing String	${ALL_LOG}	dump_frame
    Log                     ${handler}
    Log                     ${frame}
    Should Be Empty         ${handler}
    Should Be Empty         ${frame}

*** Keywords ***

Open Serial Port
    [Arguments]     ${serial}
    Connect         ${serial}    115200
    Set Timeout    5

Close Serial Port
    Disconnect
