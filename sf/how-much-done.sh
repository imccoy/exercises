for i in *.v; do if [ -f "${i}o" ] ; then echo "yes"; else echo no; fi; done | sort | uniq -c
