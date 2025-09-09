#!/usr/bin/env python3

# Goal
#
# Merge a client log and a server log to produce a complete trace, i.e. a
# sequence of specification states that forms a behavior. The trace is
# "replayable" by a dedicated TLA+ specification (see
# https://TODO/-/TransferTrace.tla).
# We want to ensure that the client and the server implementations respect the
# specification (see
# https://TODO/TransferMessage.tla)
# What we really do is checking that a particular implementation run respects
# the specification. The fact that a particular run is OK does not prove that
# the implementation is correct, so this approach only strengthens our
# confidence in the implementation. The greater number of runs are validated,
# the greater the confidence.
#
#
# Algorithm
#
# - read the client and server logs into two list of strings (one string by
# line).
#
# - parse each line into timestamp × event × dictVars
#
# - concatenate the two lists
#
# - sort the concatenated list by ascending timestamps
#
# - create a dictionary d with the specification variables and their initial
# values
#
# - for each entry e of the concatenated list:
#
#   - write e's variables into d
#
#   - print d in a formatted manner: <<val1, ...>>, \* <event>, <timestamp>

import sys
from dataclasses import dataclass
from typing import Dict, List, Tuple
from pathlib import Path

@dataclass
class Entry:
    timestamp: int
    event: str
    vars: Dict[str, str]

def parse(lines: List[str], renaming: Dict[str, str]) -> List[Entry]:
    def rename(s: str) -> str:
        return renaming[s] if s in renaming else s
    def d(fields: List[str]) -> Dict[str, str]:
        return dict((rename(kv[0]), kv[1]) for kv in (f.split('=') for f in fields))
    return [Entry(int(f[0]), f[1], d(f[2:])) for f in (l[:-1].split(':') for l in lines)]

def formatEntry(e: Entry, vars: Dict[str, str], last: bool) -> str:
    if e.event == 'DeviceSendsListRequest':
        vars['request'] = '[op |-> "list"]'
    elif e.event == 'DeviceSendsGetRequest':
        vars['request'] = f'[op |-> "get", id |-> {vars["id"]}]'
    elif e.event in ('DeviceReceivesListReply', 'DeviceReceivesGetReply'):
        vars['reply'] = 'NoReply'
    elif e.event == 'ServerHandlesListRequest':
        vars['request'] = 'NoRequest'
        vars['reply'] = f'[op |-> "list", ids |-> {vars["ids"]}]'
    elif e.event == 'ServerHandlesGetRequest':
        vars['request'] = 'NoRequest'
        vars['reply'] = f'[op |-> "get", pack |-> {vars["pack"]}]'

    comma = "" if last else ","
    return fr"<<{vars['devicePacks']}, {vars['selectedPack']}, {vars['knownIds']}, {vars['serverPacks']}, {vars['serverUnsentPacks']}, {vars['request']}, {vars['reply']}>>{comma} (* {e.event} ({e.timestamp}) *)"

def readPack(filepath: Path) -> Tuple[int, str, int]:
    tokens = filepath.read_text().split(' ')
    if len(tokens) != 3:
        raise Exception(f"Wrong format in file {filepath}. Expected 3 space-separated fields.")
    return (int(tokens[0]), tokens[1], int(tokens[2]))

def formatPack(pack: Tuple[int, str, int]) -> str:
    return f'<<{pack[0]},"{pack[1]}",{pack[2]}>>'

def main(script_name: str, args: List[str]) -> int:
    if len(args) != 3:
        print(f"Usage: {script_name} <initial_pack_file> <client_log_file> <server_log_file>")
        return 1
    entries = parse(open(args[1]).readlines(), {'packs': 'devicePacks'}) + \
              parse(open(args[2]).readlines(), {'packs': 'serverPacks', 'unsentPacks': 'serverUnsentPacks'})
    entries.sort(key=lambda e: e.timestamp)
    initialPack = formatPack(readPack(Path(args[0])))
    vars = {'devicePacks': '{%s}' % initialPack, 'selectedPack': initialPack,
            'knownIds': '{}', 'serverPacks': '{%s}' % initialPack, 'serverUnsentPacks': '{}',
            'request': 'NoRequest', 'reply': 'NoReply'}
    print(r"(* <<devicePacks, selectedPack, knownIds, serverPacks, serverUnsentPacks, request, reply>> *)")
    print(formatEntry(Entry(0, "Init", {}), vars, last=False))
    i = 1
    for e in entries:
        for (k, v) in e.vars.items():
            vars[k] = v
        print(formatEntry(e, vars, last=i == len(entries)))
        i = i + 1
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[0], sys.argv[1:]))
