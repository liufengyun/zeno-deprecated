  nop
  loadi 65

start:
  store 0
  subi 122
  brz end
  addi 122
  addi 1
  br start


end:
  exit