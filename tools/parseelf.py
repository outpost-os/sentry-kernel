#!/usr/bin/env python3

import os
import sys
import lief
import json

# Define basic binary info dict
if __name__ == '__main__':
    binary = lief.parse(sys.argv[1])
    bindict = {'text': {'vaddr':0, 'size':0},
               'data': {'vaddr':0, 'laddr':0, 'size':0},
               'bss': {'vaddr':0, 'size':0}};

    for section in binary.sections:
        if section.name == '.text':
            bindict['text']['vaddr'] += section.virtual_address
            bindict['text']['size'] += section.size
        if section.name == '.ARM':
            bindict['text']['vaddr'] += section.virtual_address
            bindict['text']['size'] += section.size
        if section.name == '.data':
            bindict['data']['vaddr'] = section.virtual_address
            bindict['data']['laddr'] = binary.get_symbol('_sidata').value
            bindict['data']['size'] = section.size
        if section.name == '.bss':
            bindict['bss']['vaddr'] = section.virtual_address
            bindict['bss']['size'] = section.size
    with open(os.path.splitext(sys.argv[1])[0] + '.json', 'w') as outfile:
        json.dump(bindict, outfile)
