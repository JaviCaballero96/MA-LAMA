#! /usr/bin/env python
# -*- coding: latin-1 -*-

import sys
import os.path
import re

from . import parser

from . import tasks

def parse_pddl_file(filetype, filename):
    try:
        return parser.parse_nested_list(open(filename))
    except IOError as e:
        raise SystemExit("Error: Could not read file: %s\nReason: %s." %
                         (e.filename, e))
    except parser.ParseError as e:
        raise SystemExit("Error: Could not parse %s file: %s\n" % (filetype, filename))

def open_pddl_file(task_filename=None, domain_filename=None):
    if task_filename is None:
        if len(sys.argv) != 5:
            raise SystemExit("Error: Need exactly four command line arguments.\n"
                             "Usage: %s <domain.pddl> <task.pddl> <time_to_search> <agent_decomp(y/n)>" % sys.argv[0])

        task_filename = sys.argv[-3]
        print("\n" + task_filename + "\n")
        if len(sys.argv) == 5:
            domain_filename = sys.argv[1]
            time_value = sys.argv[3]
            if sys.argv[4] == "y":
                agent_decomp = True
            else:
                agent_decomp = False
        else:
            time_value = sys.argv[2]
            if sys.argv[3] == "y":
                agent_decomp = True
            else:
                agent_decomp = False

    if not domain_filename:
        dirname, basename = os.path.split(task_filename)
        domain_filename = os.path.join(dirname, "domain.pddl")
        if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
            domain_filename = os.path.join(dirname, basename[:4] + "domain.pddl")
        if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
            domain_filename = os.path.join(dirname, basename[:3] + "-domain.pddl")
        if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
            domain_filename = os.path.join(dirname, "domain_" + basename)
        if not os.path.exists(domain_filename) and basename.endswith("-problem.pddl"):
            domain_filename = os.path.join(dirname, basename[:-13] + "-domain.pddl")
        if not os.path.exists(domain_filename):
            raise SystemExit("Error: Could not find domain file using "
                             "automatic naming rules.")

    domain_pddl = parse_pddl_file("domain", domain_filename)
    task_pddl = parse_pddl_file("task", task_filename)
    return tasks.Task.parse(domain_pddl, task_pddl), time_value, agent_decomp

if __name__ == "__main__":
    open_pddl_file().dump()
