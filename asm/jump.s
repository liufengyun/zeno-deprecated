  nop
  loadi 65

start:
  subi 122
  brp end
  addi 122
  store 0
  addi 1
  br start


end:
  exit