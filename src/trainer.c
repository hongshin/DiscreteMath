#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>

typedef struct _Word{
	char word[30];
	int p_num;
	int n_num;
}Word;

void token(char *s1);
void b_Sort(Word *word[], int len);
int stop(char* s1);
int check(char* buf, Word* word[], int len);
int p_check(char* buf, Word* word[], int len);
int n_check(char* buf, Word* word[], int len);
int reduction(int po, int ne);

int main(int argc, char* argv[]){	
	char* po;
	char* ne;
	if(argc!=3){
                printf("Usage : %s <Positive_m> <Negative_m> \n", argv[0]);
                exit(1);
        }
	po = argv[1];
	ne = argv[2];

	FILE * fp = fopen(po,"r");
	FILE * fp2 = fopen(ne,"r");

	FILE * write = fopen("po_out", "w");
	FILE * write2 = fopen("ne_out", "w");
	int n = 0;
	int m = 0;
	int index = 0;
	int index2 = 0;
	char buf[128];
	int len=0;
//	char** word = malloc(sizeof(char*) * 4096);
	Word* word[4096];
	
	while(EOF != fscanf(fp,"%s",buf)){
//		fscanf(fp,"%s", buf);
		token(buf);	 // Tokenization
		word[n] = (Word*)malloc(sizeof(Word));
		strcpy(word[n]->word,buf);
//		printf("[DEBUG]word%d: %s\n", n+1, word[n]);
//		printf("%s\n", word[n]->word);
		fprintf(write, "%s", word[n]->word);
		fprintf(write, "\n");
		n++;	
	}
	fclose(write);
	fclose(fp);
	
	printf("[DEBUG]N: %d\n", n); 
	for(int i=0; i<n; i++){
		free(word[i]);
	}
	
	while(EOF != fscanf(fp2,"%s",buf)){
//		fscanf(fp2,"%s", buf);
		token(buf);	 // Tokenization
		word[m] = (Word*)malloc(sizeof(Word));
		strcpy(word[m]->word,buf);
		fprintf(write2, "%s", word[m]->word);
		fprintf(write2, "\n");
		m++;	
	}
	fclose(write2);
	fclose(fp2);


	printf("[DEBUG]M: %d\n", m); 
	for(int i=0; i<m; i++){
		free(word[i]);
	}

	FILE * fin = popen("./stemmer < po_out","r");      // Nomalization
	FILE * fin2 = popen("./stemmer < ne_out", "r");

	while(EOF != fscanf(fin,"%s",buf)){
//                fscanf(fin,"%s", buf);       
//		printf("[DEBUG] After s: %s\n", buf);        
		if(stop(buf)){			// Stopwrod, vocabulary 1
			if(index==0){	
				word[index] = (Word*)malloc(sizeof(Word));
				word[index]->p_num = 0;
				word[index]->n_num = 0;
				strcpy(word[index]->word, buf);
				word[index]->p_num = word[index]->p_num+1;	
				index++;
			}
			else{
				if(p_check(buf,word,index)){
					continue;
				}
				else{
					word[index] = (Word*)malloc(sizeof(Word));
					word[index]->p_num = 0;
					word[index]->n_num = 0;
                                	strcpy(word[index]->word, buf);
                                	word[index]->p_num = word[index]->p_num +1;
   //			printf("[DEBUG] word[%d]:%s\n ", index, word[index]->word);
   //			printf("[DEBUG] word[%d]의 p_num:%d\n ", index, word[index]->p_num);
                                	index++;
				}
			}
		}
		else{
			continue;
		}	
        }

	while(EOF != fscanf(fin2,"%s",buf)){
            //    fscanf(fin2,"%s", buf);                
		if(stop(buf)){			// Stopwrod, vocabulary 1
			if(index==0){	
			}
			else{
				if(n_check(buf,word,index)){
					continue;
				}
				else{
					word[index] = (Word*)malloc(sizeof(Word));
					word[index]->p_num = 0;
					word[index]->n_num = 0;
                                	strcpy(word[index]->word, buf);
                                	word[index]->n_num = word[index]->n_num +1;
   //			printf("[DEBUG] word[%d]:%s\n ", index, word[index]->word);
  // 			printf("[DEBUG] word[%d]의 n_num:%d\n ", index, word[index]->n_num);
                                	index++;
				}
			}
		}
		else{
			continue;
		}	
        }
	fclose(fin);
	fclose(fin2);

	FILE * trainer = fopen("trainer", "w");

	for(int i=0; i<index; i++){
               printf("[DEBUG]word[%d]: %s",i, word[i]->word);
 	       printf("  %d", word[i]->p_num);
               printf("  %d\n", word[i]->n_num);
		if(!reduction(word[i]->p_num, word[i]->n_num)){
			fprintf(trainer, "%s", word[i]->word);
			fprintf(trainer, " %d %d\n", word[i]->p_num, word[i]->n_num);
		}
	}
	
	fclose(trainer);	
	for(int i=0; i<index; i++){
		free(word[i]);
	}

	return 0;
}

void token(char *s1){;
	while(*s1!='\0'){
	        if(*s1>=97 && *s1<=122){
        	    s1++;
        	}
        	else if(*s1>=65 && *s1<=90){
        	   *s1+=32;
        	    s1++;
        	}
        	else{
	            strcpy(s1, s1+1);
        	 }
  }
}

void b_Sort(Word *word[], int len){

   char temp[128];

    for(int i = len-1; i >0; i--){
        for(int t = 0; t < i; t++){
            int check = strcmp(word[t]->word,word[t+1]->word); 
            if(check>0){ 
                strcpy(temp, word[t]->word); 
                strcpy(word[t]->word,word[t+1]->word);
                strcpy(word[t+1]->word,temp); 
            }
        }
    }
}

int stop(char* s1){
	if(!strcmp(s1, "a")) return 0;
	if(!strcmp(s1, "an")) return 0;
	if(!strcmp(s1, "the")) return 0;
	if(!strcmp(s1, "you")) return 0;
	if(!strcmp(s1, "i")) return 0;
	if(!strcmp(s1, "my")) return 0;
	if(!strcmp(s1, "me")) return 0;
	if(!strcmp(s1, "in")) return 0;
	if(!strcmp(s1, "it")) return 0;
	if(!strcmp(s1, "to")) return 0;
	if(!strcmp(s1, "your")) return 0;
	if(!strcmp(s1, "to")) return 0;
	if(!strcmp(s1, "on")) return 0;
	if(!strcmp(s1, "by")) return 0;
	if(!strcmp(s1, "of")) return 0;
	if(!strcmp(s1, "and")) return 0;
	if(!strcmp(s1, "about")) return 0;
	if(!strcmp(s1, "they")) return 0;
	if(!strcmp(s1, "that")) return 0;
	if(!strcmp(s1, "was")) return 0;
	if(!strcmp(s1, "are")) return 0;
	if(!strcmp(s1, "mine")) return 0;
	if(!strcmp(s1, "am")) return 0;
	if(!strcmp(s1, "is")) return 0;
	if(!strcmp(s1, "he")) return 0;
	if(!strcmp(s1, "his")) return 0;
	if(!strcmp(s1, "she")) return 0;
	if(!strcmp(s1, "her")) return 0;
	if(!strcmp(s1, "for")) return 0;
	if(!strcmp(s1, "would")) return 0;
	if(!strcmp(s1, "at")) return 0;
	if(!strcmp(s1, "us")) return 0;
	if(!strcmp(s1, "were")) return 0;
	if(!strcmp(s1, "been")) return 0;
	if(!strcmp(s1, "we")) return 0;
	if(!strcmp(s1, "when")) return 0;
	if(!strcmp(s1, "what")) return 0;
	if(!strcmp(s1, "who")) return 0;
	if(!strcmp(s1, "where")) return 0;
	if(!strcmp(s1, "all")) return 0;
	if(!strcmp(s1, "be")) return 0;
	if(!strcmp(s1, "do")) return 0;
	if(!strcmp(s1, "if")) return 0;
	if(!strcmp(s1, "from")) return 0;
	if(!strcmp(s1, "or")) return 0;
	if(!strcmp(s1, "how")) return 0;
	if(!strcmp(s1, "will")) return 0;
	if(!strcmp(s1, "have")) return 0;
	if(!strcmp(s1, "has")) return 0;
	if(!strcmp(s1, "had")) return 0;
	if(!strcmp(s1, "did")) return 0;
	if(!strcmp(s1, "but")) return 0;
	if(!strcmp(s1, "just")) return 0;
	if(!strcmp(s1, "our")) return 0;
	if(!strcmp(s1, "this")) return 0;
	if(!strcmp(s1, "there")) return 0;

// --------------------------

	if(!strcmp(s1, "dm")) return 0;
	if(!strcmp(s1, "twitter")) return 0;
	if(!strcmp(s1, "usairway")) return 0;
	if(!strncmp(s1, "http", 3)) return 0;
	return 1;
}

int p_check(char* buf, Word* word[], int len){
        for(int i=0; i<len; i++){
                if(!strcmp(word[i]->word, buf)){
                 //     	printf("[DUBUG] %s는 중복!\n", word[i]->word);
			word[i]->p_num=word[i]->p_num+1; 
  		//	printf("[DEBUG] word[%d]:%s\n ", i, word[i]->word);
   		//	printf("[DEBUG] word[%d]의 p_num:%d\n ", i, word[i]->p_num);
                        return 1;
                }
        }
        return 0;
}

int n_check(char* buf, Word* word[], int len){
        for(int i=0; i<len; i++){
                if(!strcmp(word[i]->word, buf)){
 		//	printf("[DUBUG] %s는 중복!\n", word[i]->word);
                        word[i]->n_num=word[i]->n_num+1;
                 //       printf("[DEBUG] word[%d]:%s\n ", i, word[i]->word);
                 //       printf("[DEBUG] word[%d]의 p_num:%d\n ", i, word[i]->n_num);
                        return 1;
                }
        }
        return 0;
}

int reduction(int po, int ne){
        if(po<=1 && ne<=1){
                return 1;
        }
        return 0;
}


