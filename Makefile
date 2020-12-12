all:
	gcc -g -o euler graph.c euler.c
	gcc -g -o dijkstra graph.c dijkstra.c
	gcc -g -o test graph.c test.c
