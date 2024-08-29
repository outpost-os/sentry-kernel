# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

*** Settings ***

Documentation   Sentry Autotest report generation
...             Parse autotest output on serial port and analyse its content

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

    ${read_all}             Read Until  terminator=AUTOTEST END
    Close Serial Port
    ${read_AT}              Get Lines Containing String     ${read_all}	[AT]
    Set Suite Variable      ${AT_LOG}  ${read_AT}
    Should Contain          ${read_AT}    ${PROMPT}
    ${SoC_Line}             Get Lines Containing String     ${read_all}      _entrypoint: booting on SoC
    ${SoC}                  Fetch From Right    ${SoC_Line}     ${SPACE}
    Log   ${read_all}
    Log   ${read_AT}
    Set Test Message        Autotest executed on SoC ${SoC}


AT Yield
    [Documentation]         Parse yield API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_yield
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Get Handle
    [Documentation]         Parse handle API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_gethandle
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Signals
    [Documentation]         Parse signals API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_signal
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT IPCs
    [Documentation]         Parse IPC API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_ipc
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            {suite}

AT KRNG
    [Documentation]         Parse KRNG API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_random
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Sleep
    [Documentation]         Parse sleep API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_sleep
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT GPIOs
    [Documentation]         Parse GPIO API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_gpio
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Cycles measurment
    [Documentation]         Parse Cycle API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_cycles
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT SHM
    [Documentation]         Parse SHM API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_shm
    Log                     ${suite}
    Should Not Be Empty     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT Map
    [Documentation]         Parse map API autotest results

    Depends on test         Load Autotest
    ${suite}                Get Lines Containing String	${AT_LOG}	test_map
    Log                     ${suite}
    Should Not Contain      ${suite}   KO
    Suite Result            ${suite}

AT DMAs
    [Documentation]     Parse DMA API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_dma
    Log                 ${suite}
    Should Not Contain  ${suite}   KO
    Suite Result        ${suite}

Autotest Totals
    [Documentation]         Calculate total numbers of Success and KOs

    Depends on test         Load Autotest
    Suite Result            ${AT_LOG}


*** Keywords ***

Open Serial Port
    Connect        /dev/ttyACM0    115200
    Set Timeout    20

Close Serial Port
    Disconnect

Suite Result
    [Arguments]         ${suite}

    ${success}          Get Lines Containing String	${suite}	SUCCESS
    ${success_num}      Get Line Count  ${success}
    ${KO}          Get Lines Containing String	${suite}	KO
    ${KO_num}      Get Line Count  ${KO}
    Set Test Message    Success: ${success_num}, KOs: ${KO_num}
