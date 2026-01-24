file ./build/test/racfed_eddi_s-branch_eddi/racfed_eddi_s-branch_eddi.out
break *0x0000000000001304
run
set $pc = $pc + 6
continue
quit