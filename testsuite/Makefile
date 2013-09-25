SHELL:=/bin/bash -O extglob
FILE=
FORMULA=

default:
	@echo '-- Testsuit examples --'
	@echo 'Usage: make <target>'
	@echo 'Target:'
	@echo '	pacemaker : pacemaker example'
	@echo '	micro : microwave example'
	@echo '	micro_ob : microwave example with observer'
	@echo '	robot_c : robot motion controller'
	@echo '	conveyor : conveyor example'
	@echo '	clean : removing generated files'

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

%:
	systemjc -promela $(FILE).pml $(FILE).sysj -formula '$(FORMULA)'
	spin -a $(FILE).pml
	@echo 'Checking the property $(FORMULA)'
	gcc-4 -DMEMLIM=1024 -O2 -DXUSAFE -w -o pan pan.c
	./pan -m10000 -a -f
clean:
	rm -vf !(*.sysj|Makefile)
