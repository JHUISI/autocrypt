import sys, time

dir_above = '../auto-tools/'
sdl_pkg = '../auto-tools/sdlparser/'

if dir_above not in sys.path:
   sys.path.append(dir_above)
if sdl_pkg not in sys.path:
   sys.path.append(sdl_pkg)

