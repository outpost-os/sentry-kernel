# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

*** Settings ***

Documentation   Read back autotest serial output

Library         SerialLibrary
Library         String
Library         DependencyLibrary

Suite Setup     Open Serial Port
Suite Teardown  Close Serial Port

*** Variables ***

${PROMPT}          [AT]

*** Test Cases ***

Load Autotest
    [Documentation]     Read autotest content from serial line

    ${read_all}         Read Until  terminator=AUTOTEST END
    ${read_AT}          Get Lines Containing String	${read_all}	[AT]
    Set Suite Variable  ${AT_LOG}  ${read_AT}
    Should Contain      ${read_AT}    ${PROMPT}
    Log   ${read_AT}

AT Yield
    [Documentation]     Parse yield API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_yield
    Log                 ${suite}
    Should Not Contain  ${suite}   FAILURE
    Suite Result        ${suite}   

AT Get Handle
    [Documentation]     Parse handle API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_gethandle
    Log                 ${suite}
    Should Not Contain  ${suite}   FAILURE
    Suite Result        ${suite}   

AT Signals
    [Documentation]     Parse signals API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_signal
    Log                 ${suite}
    Should Not Contain  ${suite}   FAILURE
    Suite Result        ${suite}   

AT IPCs
    [Documentation]     Parse IPC API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_ipc
    Log                 ${suite}
    Should Not Contain  ${suite}   FAILURE
    Suite Result        ${suite}   

AT KRNG
    [Documentation]     Parse KRNG API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_random
    Log                 ${suite}
    Should Not Contain  ${suite}   FAILURE
    Suite Result        ${suite}   

AT Sleep
    [Documentation]     Parse sleep API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_sleep
    Log                 ${suite}
    Should Not Contain  ${suite}   FAILURE
    Suite Result        ${suite}   

AT GPIOs
    [Documentation]     Parse GPIO API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_gpio
    Log                 ${suite}
    Should Not Contain  ${suite}   FAILURE
    Suite Result        ${suite}   

AT Cycles measurment
    [Documentation]     Parse Cycle API autotest results

    Depends on test     Load Autotest
    ${suite}            Get Lines Containing String	${AT_LOG}	test_cycles
    Log                 ${suite}
    Should Not Contain  ${suite}   FAILURE
    Suite Result        ${suite}

Autotest Totals
    [Documentation]     Calculate total numbers of Success and Failures

    Depends on test     Load Autotest
    Suite Result        ${AT_LOG}
    

*** Keywords ***

Open Serial Port
    Connect        /dev/ttyUSB0    115200
    Set Timeout    10

Close Serial Port
    Disconnect

Suite Result
    [Arguments]         ${suite}

    ${success}          Get Lines Containing String	${suite}	SUCCESS
    ${success_num}      Get Line Count  ${success}
    ${failure}          Get Lines Containing String	${suite}	FAILURE
    ${failure_num}      Get Line Count  ${failure}
    Set Test Message    Success: ${success_num}, Failures: ${failure_num}
 
