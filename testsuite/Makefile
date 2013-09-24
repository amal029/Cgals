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
	@echo '	clean : removing generated files'
pacemaker: 
FILE = pacemaker
FORMULA = [] (CD0_TLRITAVI -> <> CD1_oVP)
pacemaker:
	make run 

micro:
FILE = microwave_oven
FORMULA =[](CD0_HEAT -> <> CD0_LIGHT) 
micro:
	make run

micro_ob:
FILE = observer_based_verification_of_microwave_oven
FORMULA = [] !CD0_VIOLATED
micro_ob:
	make run

run:
	systemjc -promela $(FILE).pml $(FILE).sysj -formula '$(FORMULA)'
	spin -a $(FILE).pml
	# Checking the property '[] (CD0_TLRITAVI -> <> CD1_oVP)'
	gcc-4 -DMEMLIM=1024 -O2 -DXUSAFE -w -o pan pan.c
	./pan -m10000 -a -f
clean:
	rm -vf !(*.sysj|Makefile)
