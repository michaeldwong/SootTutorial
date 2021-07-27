
import argparse

def breakdown_line(line):
    words = line.split()
    assert(len(words) == 11 or len(words) == 12)
    date_array = words[1].split(':')
    # Read/write profiling data
    if len(words) == 11:
        return ProfilingEntry( 
            int(date_array[0]), int(date_array[1]), float(date_array[2]), 
                words[6], words[7], int(words[10].strip())
               )
    # Function call profiling data
    return ProfilingEntry(
            int(date_array[0]), int(date_array[1]), float(date_array[2]), 
                words[6], words[7], int(words[11].strip())
           )

def is_profiling_data(line):
    return "<SOOT_PROFILING>" in line

def write_file(f, names_to_read_count, names_to_write_count, names_to_function_count):

    for name in names_to_read_count:
        f.write(f'{name} -> {names_to_read_count[name]} reads\n')
    for name in names_to_read_count:
        f.write(f'{name} -> {names_to_read_count[name]} writes\n')
    for name in names_to_read_count:
        f.write(f'{name} -> {names_to_read_count[name]} function calls\n')
    f.write('\n==============\n')

def parse(log_file, out_file):
    names_to_read_count = {}
    names_to_write_count = {}
    names_to_function_count = {}
    minute_last_written = -1
    second_last_written = -1
    with open(log_file, 'r') as f:
        lines = f.readlines()
        for line in lines:
            if not is_profiling_data(line):
                continue
            data = breakdown_line(line)
            if data.operation == 'read':
                names_to_read_count[data.name] = data.count
            elif data.operation == 'write':
                names_to_write_count[data.name] = data.count
            elif data.operation == 'function':
                names_to_function_count[data.name] = data.count
            else: 
                print('Unknown operation: ', data.operation)
                continue
            if second_last_written == -1 or minute_last_written == -1:
                second_last_written = data.seconds
                minute_last_written = data.minute
                continue
            if data.seconds - second_last_written >= 10 or \
                (data.seconds < second_last_written and (60 - second_last_written + data.seconds >= 10)):
                print('Writing')
                print(f'{data.minute} : {data.seconds}  -- {data.name} {data.operation} {data.count}')
                with open(out_file, 'a') as f:
                    f.write(f'Time: {data.hour}:{data.minute}:{data.seconds}\n')
                    write_file(f, names_to_read_count, names_to_write_count, names_to_function_count)
                second_last_written = data.seconds
                minute_last_written = data.minute
            
class ProfilingEntry:
    def __init__(self, hour, minute, seconds, name, operation, count):
        self.hour = hour
        self.minute = minute
        self.seconds = seconds
        self.name = name
        self.operation = operation
        self.count = count

def main():
    ap = argparse.ArgumentParser() 
    ap.add_argument('log_file')
    ap.add_argument('out_file')
    args = ap.parse_args()
    parse(args.log_file, args.out_file)
    
if __name__ == '__main__':
    main()
