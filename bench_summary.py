#!/usr/bin/python
import sys

stats = {}
stats['total'] = []
stats['precise'] = []
stats['imprecise'] = []
stats['false-positives'] = []
stats['undetected'] = []

for line in open(sys.argv[1]):
    line = line.rstrip()
    if line[0] == '#':
        continue
    cols = line.split('|')
    name = cols[0]
    if cols[1] != 'KO':
        print "Warning: outcome of %s is %s, skipping it" % (name, cols[1])
        continue
    expected_error = cols[2]
    real_errors = cols[3].split(',')
    spurious_errors = cols[4].split(',')

    stats['total'].append((name,real_errors))
    if set([expected_error]) == set(real_errors):
        if expected_error in spurious_errors:
            stats['false-positives'].append((name,real_errors))
        else:
            stats['precise'].append((name,real_errors))
    elif expected_error in real_errors:
        if expected_error in spurious_errors:
            stats['false-positives'].append((name,real_errors))
        else:
            stats['imprecise'].append((name,real_errors))
    else:
        if expected_error in spurious_errors:
            stats['false-positives'].append((name,real_errors))
        else:
            stats['undetected'].append((name,real_errors))

for field in ['undetected', 'imprecise', 'false-positives']:
    print "===================="
    print "%s:" % field
    for name,_ in stats[field]:
        print "  %s" % name

def average(l):
    if not(len(l)):
        return "N/A"
    else:
        return "%6.1f" % (reduce(lambda acc,x: acc+x,l,0)/float(len(l)))

def mymax(l):
    if not(len(l)):
        return 0
    else:
        return max(l)

def format_stat(field):
    global stats
    lista = stats[field]
    errors = map(lambda x: len(x[1]),lista)
    locations = map(lambda x: len(set(x[1])),lista)
    return r'%-15s & %6d & %6s & %6d & %6s & %6d & %6.1f\%% \\' % \
            (field, len(lista), average(locations),mymax(locations),
            average(errors),mymax(errors),float(len(lista)) /
            len(stats['total']) * 100)

print "\n"
print format_stat('precise')
print format_stat('imprecise')
print format_stat('false-positives')
print format_stat('undetected')
print r'\hline'
print format_stat('total')
