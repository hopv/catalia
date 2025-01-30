'''
# How To Bench
0. Install https://github.com/moratorium08/benchmark_scripts/tree/main/bench2
1. Place this at path/to/hoice/scripts/absadt.py
2. (Fixme) Clone hopdr at /home/katsura/github.com/moratorium08
3. Go hopdr/hopdr/benchmark/ and Run ./gen.sh
4. Go back to path/to/hoice/scripts
5. python3 absadt.py 24comp_ADT-LIA --n-threads 4 --timeout 300
'''

from katsura_bench import *

class AbsAdt(Benchmarker):
    def pre_cmd(self):
        return 'cargo build --release'
    
    def gen_cmd(self, file: str):
        print('file', file)
        return f'../target/release/hoice {file}'
      
    def parse_stdout(self, stdout):
      result_data = dict()
      results = stdout.split("\n")
      stdouts = []
      warnings = ""
      for line in results:
          if line.startswith("; "):
              warnings += line + "\n"
          else:
              stdouts.append(line)
      stdout = stdouts[0]
      result_data['result'] = 'invalid' if 'unsat' in stdout else 'valid' if 'sat' in stdout else 'fail' 
      result_data['warnings'] = warnings
      return result_data
    
    def base_dir(self):
        return '/home/katsura/github.com/moratorium08/hopdr/hopdr/benchmark'


do_bench(AbsAdt())
