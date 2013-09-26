SHELL:=/bin/bash -O extglob
FILE=
FORMULA=
define README
-- Testsuit examples --
Usage: make <target>
Target:
	pacemaker : pacemaker example
	micro : microwave example
	micro_ob : microwave example with observer
	robot_c : robot motion controller
	conveyor : conveyor example
	washing : washing machine example
	clean : removing generated files
endef
export README

default:
	echo "$$README"

pacemaker: FILE = pacemaker
pacemaker: FORMULA = [] (CD0_TLRITAVI -> <> CD1_oVP)

micro: FILE = microwave_oven
micro: FORMULA =[](CD0_HEAT -> <> CD0_LIGHT) 

micro_ob: FILE = observer_based_verification_of_microwave_oven
micro_ob: FORMULA = [] !CD0_VIOLATED

robot_c: FILE = robot_motion_controller
robot_c: FORMULA = [] (!CD1_VIOLATED)

conveyor: FILE = conveyor_belt
conveyor: FORMULA = [] (!CD0_VIOLATED && !CD1_VIOLATED)

washing: FILE = washing
washing: FORMULA = [] !(CD0_WASHING && CD0_DRYING)

abort_imm: FILE=abort_imm
abort_imm: FORMULA=<> !CD0_B

%:
	systemjc -promela $(FILE).pml $(FILE).sysj -formula '$(FORMULA)'
	spin -a $(FILE).pml
	@echo 'Checking the property $(FORMULA)'
	gcc-4 -DMEMLIM=1024 -O2 -DXUSAFE -w -o pan pan.c
	./pan -m10000 -a -f
clean:
	rm -vf !(*.sysj|Makefile)
