#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

struct node {
	void * element ;
	struct node * next ; 
} ;

struct linkedlist {
	int unit ;
	struct node * last ;
} ;


typedef struct node node_t ;
typedef struct linkedlist linkedlist_t ;

linkedlist_t * 
linkedlist_alloc (int unit)  ;

void
linkedlist_free (linkedlist_t * l) ;

int 
linkedlist_length (linkedlist_t * l) ;

void
linkedlist_insert_first (linkedlist_t * l, void * e) ;

void
linkedlist_insert_last (linkedlist_t * l, void * e) ;

int
linkedlist_remove (linkedlist_t * l, node_t * n) ;

int
linkedlist_remove_first (linkedlist_t * l, void * e) ;

int
linkedlist_remove_last (linkedlist_t * l, void * e) ;

int
linkedlist_get (linkedlist_t * l, int pos, void * e) ;

linkedlist_t * 
linkedlist_alloc (int unit) 
{
	linkedlist_t * l = (linkedlist_t *) malloc(sizeof(linkedlist_t)) ;
	l->unit = unit ;
	l->last = 0x0 ;	
	return l ;
}

void
linkedlist_free (linkedlist_t * l)
{
	node_t * curr ;
	node_t * next ;

	if (l->last) {
		curr = l->last->next ; 
		do {
			node_t * next = curr->next ;
			free(curr->element) ;
			free(curr) ;
			curr = next ;
		} while (curr != l->last) ;
	}
	free(l) ;
}

int 
linkedlist_length (linkedlist_t * l)
{
	int len = 0 ;
	if (l->last) {
		node_t * curr = l->last ;
		do {
			len += 1 ;
			curr = curr->next ;
		} while (curr != l->last) ;
	}
	return len ; 
}

void
linkedlist_insert_first (linkedlist_t * l, void * e)
{
	node_t * n = (node_t *) malloc(sizeof(node_t)) ;
	n->element = malloc(l->unit) ;
	memcpy(n->element, e, l->unit) ;

	if (l->last) {
		node_t * first ;
		first = l->last->next ;
		n->next = first ;
		l->last->next = n ;
	}
	else {
		l->last = n ;
		l->last->next = n ;
	}
}

void
linkedlist_insert_last (linkedlist_t * l, void * e)
{
	node_t * n = (node_t *) malloc(sizeof(node_t)) ;
	n->element = malloc(l->unit) ;
	memcpy(n->element, e, l->unit) ;

	if (l->last) {
		node_t * first ;
		first = l->last->next ;
		n->next = first ;
		l->last->next = n ;
		l->last = n ;
	}
	else {
		l->last = n ;
		l->last->next = n ;
	}
}

int
linkedlist_remove (linkedlist_t * l, node_t * n)
{
	if (l->last == 0x0)
		return 1 ;

	node_t * prev = l->last ;
	node_t * curr = l->last->next ;
	while (curr != n && curr != l->last) {
		prev = curr ;
		curr = curr->next ;		
	}
	if (curr != n) 
		return 1 ;

	if (prev != curr) 
		prev->next = curr->next ;
	else 
		l->last = 0x0 ;
	free(curr->element) ;
	free(curr) ;
	return 0 ;
}

int 
linkedlist_remove_first (linkedlist_t * l, void * e)
{
	if (l->last == 0x0)
		return 1 ;

	node_t * first = l->last->next ;
	memcpy(e, first->element, l->unit) ;
	linkedlist_remove(l, first) ;
	return 0 ;
}

int
linkedlist_remove_last (linkedlist_t * l, void * e)
{
	if (l->last == 0x0)
		return 1 ;

	node_t * last = l->last ;


	if (l->last == l->last->next) {
		l->last = 0x0 ;
	} 
	else {
		node_t * n = l->last ;
		while (n->next != l->last) {
			n = n->next ;
		}
		n->next = l->last->next ;
		l->last = n ;
	}

	memcpy(e, last->element, l->unit) ;
	free(last->element) ;
	free(last) ;
	return 0 ;
}

int
linkedlist_get (linkedlist_t * l, int pos, void * e)
{
	if (pos < 0 || l->last == 0x0)
		return 1 ;

	int i = 0 ;
	node_t * n = l->last->next ;
	while (i < pos && n != l->last) {
		n = n->next ;
		i++ ;
	}
	if (i != pos)
		return 1 ;

	memcpy(e, n->element, l->unit) ;
	return 0 ;
}

void RemoveFirst(char *buf)
{
    int i = 0;
    for (i = 1; buf[i]; i++)
    {
        buf[i - 1] = buf[i];
    }
    buf[i - 1] = '\0';
}

typedef struct{
    char string[129];
    int m;
} task;

int main(){
    char pe[129];
    int len=0;
    char str[5][129];
   
    scanf("%s", pe);

    while(pe[len] != '\0'){
                len++;
    }	

    for(int i=0;i<5;i++){
        scanf("%s", str[i]);
    }

    linkedlist_t * l ;
    linkedlist_t * s ;
    l = linkedlist_alloc(sizeof(char)) ;
    s = linkedlist_alloc(sizeof(task));

    for(int i=0;i<5;i++){
        for(int j=0;j<len;j++){
        	linkedlist_insert_last(l, &pe[j]) ;
        }
        task first;
        strcpy(first.string,str[i]);		
        first.m = 0;      
        linkedlist_insert_last(s, &first);

        while(linkedlist_length(l) != 0){
        	    char p;
		    linkedlist_remove_first(l, &p);
				if(islower(p)){
	 				int c_len = linkedlist_length(s);
                                        for(int k=0;k<c_len;k++){
                                                task load;
                                                linkedlist_remove_first(s,&load);
                                                if(load.string[0] == p){
                                                        task next;
                                                        strcpy(next.string, load.string);
                                                	RemoveFirst(next.string);
                                                	linkedlist_insert_last(s, &next);
                                                }
                                        }
				}
				else if(p=='*'){
					int c_len = linkedlist_length(s);
					
					for(int k=0;k<c_len;k++){
                  				task a;
                    				linkedlist_remove_first(s, &a);
							if(strlen(a.string) == 0){
								linkedlist_insert_last(s, &a);
							}
							else{
								int length = strlen(a.string);
								int numm = 0;	
								while(numm < length+1){
									task next;
									strcpy(next.string, a.string);
									for(int z=0; z<length-numm; z++){
										next.string[z] = next.string[z+numm];
									}
									int d =1;
									while(d<numm+1){
										next.string[strlen(a.string)-d] = '\0';
 										d++; 
									}
								linkedlist_insert_last(s, &next);
								numm++;
								}
							}		
					}
				}
				else if(p=='!'){
					int c_len = linkedlist_length(s);
					for(int k=0;k<c_len;k++){
                    				task b;
                    				linkedlist_remove_first(s,&b);
						linkedlist_insert_last(s,&b);
						if(strlen(b.string) != 0){
							task next;
							strcpy(next.string, b.string);
							RemoveFirst(next.string);
                        				linkedlist_insert_last(s, &next);	
						}
               				 }
				}

			   	else if(p == '?'){
					int c_len = linkedlist_length(s);
					for(int k=0;k<c_len;k++){
                    				task c;
                    				linkedlist_remove_first(s,&c);
						
						task next;
						strcpy(next.string, c.string);
						RemoveFirst(next.string);	
                     				linkedlist_insert_last(s, &next);		
						}
                		}
				
				else if(p=='['){
	/*				linkedlist_t * queue;
					queue = linkedlist_alloc(sizeof(task));
					int c_len = linkedlist_length(s);
					for(int k=0;k<c_len;k++){
						task d;
						linkedlist_remove_first(s,&d);
						linkedlist_insert_last(queue, &d);
					}
					while(1){
						linkedlist_remove_first(l, &p);
						if(p == ']')
							 break;

						int c_leng = linkedlist_length(queue);
						for(int k=0;k<c_len;k++){
							task e;
							linkedlist_remove_first(queue,&e);
							if(e.string[0] == p){
								task next;
								strcpy(next.string, e.string);
								RemoveFirst(next.string);
								linkedlist_insert_last(s, &next);
							}
							else {
								linkedlist_insert_last(queue, &e);
							}
						}
					}
				}
	*/	
					char mem[129] = {0,};
					int c_len = linkedlist_length(s);
					int index =0;
                                        while(1){
                                                char firstt;
                                                linkedlist_remove_first(l,&firstt);
                                          		if(firstt==']')
                                                  		break;
                                                if(islower(firstt)){
							mem[index] = firstt;
                                      			index++;
						}
                                        }
	
					for(int k=0; k<c_len; k++){
						task e;
						linkedlist_remove_first(s,&e);
						if(strchr(mem, e.string[0])){
							task next;
                                                      	strcpy(next.string,e.string);
                                                       	RemoveFirst(next.string);
                                                       	linkedlist_insert_last(s, &next);
						}
					}	
				} 
				else{
					break;
				}
        		}

        	task result;
		int tof=0;
		while(linkedlist_length(s) != 0){
			linkedlist_remove_first(s,&result);
			if(strlen(result.string) == 0){
				tof += 1;
			}
		}
		if(tof != 0){
            		printf("true\n");
        	}
       		else {
			 printf("false\n");
		}
    	}

	linkedlist_free(l);
	linkedlist_free(s);
	return 0;
}
