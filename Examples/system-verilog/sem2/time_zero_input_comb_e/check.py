#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'time_zero_input_comb_e.sv'
EXPECTED=['10','10','10']
TB=r'''`timescale 1ns/1ps
module tb;
  logic clk,en; logic [1:0] a,b,q;
  time_zero_input_comb_e dut(.clk(clk),.en(en),.a(a),.b(b),.q(q));
  initial begin
    {clk,en,a,b}= {1'b1,1'b1,2'b01,2'b10}; #5 $display("ROW %b",dut.q);
    #5 {clk,en,a,b}= {1'b0,1'b1,2'b01,2'b10}; #5 $display("ROW %b",dut.q);
    #5 {clk,en,a,b}= {1'b1,1'b1,2'b01,2'b10}; #5 $display("ROW %b",dut.q);
    #10 $finish;
  end
endmodule'''
def rows(s): return [x.split()[1] for x in s.splitlines() if x.startswith('ROW ')]
def run(c,w): return subprocess.run(c,cwd=w,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=True,timeout=180).stdout
def main():
  with tempfile.TemporaryDirectory(prefix='sv-time-zero-input-') as td:
    w=Path(td); tb=w/'tb.sv'; tb.write_text(TB); exe=w/'sim'
    run(['iverilog','-g2012','-s','tb','-o',str(exe),str(SOURCE),str(tb)],w)
    got=rows(run(['vvp',str(exe)],w))
    if got != EXPECTED: raise RuntimeError(f'Icarus rows {got} != {EXPECTED}')
    print('Icarus Verilog 13.0: three rows MATCH')
    if shutil.which('xrun'):
      got=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],w))
      print('Xcelium Verilog 24.03-s004: '+('three rows MATCH' if got==EXPECTED else f'rows {got}'))
    else: print('Xcelium Verilog 24.03-s004: no result, xrun unavailable')
if __name__=='__main__': main()
