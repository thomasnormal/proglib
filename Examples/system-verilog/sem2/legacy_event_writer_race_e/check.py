#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
SOURCE = HERE / "legacy_event_writer_race_e.sv"
EXPECTED = ["x x", "x 0", "x 0", "0 1", "0 1", "0 0", "0 0", "0 1"]
TB = r'''`timescale 1ns/1ps
module tb;
  logic clk, rst, en, din, b;
  legacy_event_writer_race_e dut(.clk(clk), .rst(rst), .en(en), .din(din), .b(b));
  initial begin
    #10 {clk,rst,en,din,b} = {1'b0,1'b1,1'b1,1'b0,1'b0}; #5 $display("ROW %b %b",dut.q,dut.div);
    #5 {clk,rst,en,din,b} = {1'b1,1'b1,1'b1,1'b0,1'b0}; #5 $display("ROW %b %b",dut.q,dut.div);
    #5 {clk,rst,en,din,b} = {1'b0,1'b0,1'b1,1'b1,1'b0}; #5 $display("ROW %b %b",dut.q,dut.div);
    #5 {clk,rst,en,din,b} = {1'b1,1'b0,1'b1,1'b1,1'b0}; #5 $display("ROW %b %b",dut.q,dut.div);
    #5 {clk,rst,en,din,b} = {1'b0,1'b0,1'b1,1'b0,1'b0}; #5 $display("ROW %b %b",dut.q,dut.div);
    #5 {clk,rst,en,din,b} = {1'b1,1'b0,1'b1,1'b0,1'b0}; #5 $display("ROW %b %b",dut.q,dut.div);
    #5 {clk,rst,en,din,b} = {1'b0,1'b0,1'b1,1'b1,1'b0}; #5 $display("ROW %b %b",dut.q,dut.div);
    #5 {clk,rst,en,din,b} = {1'b1,1'b0,1'b1,1'b1,1'b0}; #5 $display("ROW %b %b",dut.q,dut.div);
    #10 $finish;
  end
endmodule'''
def rows(out): return [" ".join(line.split()[1:]) for line in out.splitlines() if line.startswith("ROW ")]
def run(cmd,cwd): return subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=True,timeout=180).stdout
def main():
  with tempfile.TemporaryDirectory(prefix="sv-legacy-writer-race-") as td:
    w=Path(td); tb=w/'tb.sv'; tb.write_text(TB); exe=w/'sim'
    run(['iverilog','-g2012','-s','tb','-o',str(exe),str(SOURCE),str(tb)],w)
    got=rows(run(['vvp',str(exe)],w))
    if got != EXPECTED: raise RuntimeError(f'Icarus rows {got} != {EXPECTED}')
    print('Icarus Verilog 13.0: eight rows MATCH')
    if shutil.which('xrun'):
      got=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],w))
      if got != EXPECTED: raise RuntimeError(f'Xcelium rows {got} != {EXPECTED}')
      print('Xcelium Verilog 24.03-s004: eight rows MATCH')
    else: print('Xcelium Verilog 24.03-s004: no result, xrun unavailable')
if __name__=='__main__': main()
