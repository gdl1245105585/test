# IEDA verilator 测试环境
> 使用的是 YSYXSOC 框架，基于 verilator 的仿真环境，由于原框架只有 64 位程序，所以需要修改一下，使其支持 32 位程序。


## Usage
> 大部分可以参考 README.md

### Add core
> 参考 README.md

### Compile
> 参考 README.md
```bash
./main.py -fc
```

### Run
> 不使用 README.md 中的 main.py 脚本.目前 `ysyxSOC` 框架自带的程序都是 64 位的，32 位程序的编译参考 [transplantation-doc](https://github.com/iEDA-Open-Source-Core-Project/transplantation-doc)。
> todo！：添加脚本支持一键运行

+ `ysyxSOC` 编译成功后，生成的可执行文件位于 `sim/build/emu`
```bash
❯ ./sim/build/emu --help
Emulator compiled at May  4 2023, 00:33:48
OSCPU Seasion 4 SoC Emulator
Usage:
  emu [OPTION...]

  -h, --help           print usage
  -d, --dump-wave      dump vcd(fst) format waveform when log is enabled
  -b, --log-begin arg  display log from NUM th cycle (default: 0)
  -e, --log-end arg    stop display log at NUM th cycle (default: 0)
  -t, --sim-time arg   stop simulation after NUM seconds (default: 0)
  -m, --sim-mode arg   direct sim or cosim with sdl2 to support ps2 and vga
  -i, --image arg      run with this image file
```
+ 带波形运行 rtt
```bash
/home/leesum/soc-ieda/leesum/ysyxSoC/ysyx/sim/build/emu  -d -t 1000 -m cmd -i ~/soc-ieda/leesum/transplantation-doc/prebuild_prog/bin/mem/rtthread-i-mem-riscv32-mycpu.bin
```
+ 不带波形运行 rtt
```bash
/home/leesum/soc-ieda/leesum/ysyxSoC/ysyx/sim/build/emu   -t 1000 -m cmd -i ~/soc-ieda/leesum/transplantation-doc/prebuild_prog/bin/mem/rtthread-i-mem-riscv32-mycpu.bin
```




