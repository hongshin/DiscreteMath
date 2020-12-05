#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>


typedef struct _Word{
        char word[30];
        int p_num;
        int n_num;
}Word;

void token(char* s1);
int stop(char* s1);
double cal_po(char* s1, Word* table[], int len);
double cal_ne(char* s1, Word* table[], int len);


int main(){
	char* input = malloc(sizeof(char) * 100);
	FILE * fp = fopen("trainer", "r");
	char* word[100];
	Word* table[4096];
	int n=0;
	FILE * write = fopen("txt", "w");
	char buf[128];
	double p_po=1;
	double p_ne=1;
	int index=0;
	int t_idx=0;

	while(1){
		table[t_idx] = (Word*)malloc(sizeof(Word));	
		fscanf(fp, "%s %d %d", table[t_idx]->word, &table[t_idx]->p_num, &table[t_idx]->n_num);	
			if(feof(fp)) break;
//		printf("table: %s %d %d\n", table[t_idx]->word, table[t_idx]->p_num, table[t_idx]->n_num);
		t_idx++;
	}

	scanf("%[^\n]", input);	
	printf("%s\n", input);
	char* p = strtok(input, " ");
	
	while(p != NULL){
		token(p);       // Tokenization
		word[n] = (char*)malloc(sizeof(char));	
		strcpy(word[n], p);	
		printf("[DEBUG] token: %s\n", p);
		fprintf(write, "%s\n" , p);
		p = strtok(NULL, " "); 
		n++;
	}
	
	for(int i=0; i<n; i++){
		free(word[i]);
	}

	fclose(write);

	FILE * fin = popen("./stemmer < txt","r"); // Normalization

	while(EOF != fscanf(fin,"%s",buf)){
//		fscanf(fin,"%s",buf);
		printf("[DEBUG] After Stemmer: %s\n", buf);
		if(stop(buf)){					// Stopword
			double temp=0;
			temp = cal_po(buf,table,t_idx);
			p_po = p_po*temp;
			temp = cal_ne(buf,table,t_idx);
			p_ne = p_ne*temp;
			printf("[DEBUG]포지티브: %f 네거티브: %f\n", p_po, p_ne);
		}
	}
       	
	if(p_ne >= p_po){
		printf("The Text is Negative Message\n");
	}
	else{
		printf("The Text is Non-Negative Message\n");
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

double cal_po(char* s1, Word* table[], int len){
	for(int i=0; i<len; i++){
		if(!strcmp(table[i]->word, s1)){
			printf("그 단어(%s)는positive table에 %d번 등장\n", s1, table[i]->p_num);
			double n;
			n = (double)(table[i]->p_num+1000)/(double)(len+1000);
			return n;
		}
	}
	return (double)1000/(double)(len+1000);
}

double cal_ne(char* s1, Word* table[], int len){
	for(int i=0; i<len; i++){
		if(!strcmp(table[i]->word, s1)){
			printf("그 단어(%s)는negative table에 %d번 등장\n", s1, table[i]->n_num);
			double n;
			n = (double)(table[i]->n_num+1000)/(double)(len+1000);
			return n;
		}
	}
	return (double)1000/(double)(len+1000);
}
