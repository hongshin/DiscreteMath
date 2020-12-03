#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>

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

void b_Sort(char *word[], int len){

   char temp[128];

    for(int i = len-1; i >0; i--){
        for(int t = 0; t < i; t++){
            int check = strcmp(word[t],word[t+1]); 
            if(check>0){ 
                strcpy(temp, word[t]); 
                strcpy(word[t],word[t+1]);
                strcpy(word[t+1],temp); 
            }
        }
    }
}

void stop(char* s[]){

}

struct wo{
	char* word;
	int num;
};

int main(int argc, char* argv[]){	
	char* po;
	char* ne;
	char* word_p;
	char* word_n;

	if(argc!=3){
                printf("Usage : %s <Positive_m> <Negative_m> \n", argv[0]);
                exit(1);
        }
	po = argv[1];
	ne = argv[2];
	printf("[DEBUG] positive_fname:%s negative_fname:%s \n", po,ne);

	FILE * fp = fopen(po,"r");
	FILE * write = fopen("po_out", "w");
	int n = 0;
	int index = 0;
	char buf[128];
	char* word[4096]
// = malloc(sizeof(char*) * 4096);
//	char* box = malloc(sizeof(char*) * 4096);
	while(!feof(fp)){
		fscanf(fp,"%s", buf);
		token(buf);	 // Tokenization
		word[n] = buf;
//		printf("[DEBUG]word%d: %s\n", n+1, word[n]);
	//	printf("%s\n", word[n]);
		fprintf(write, "%s", word[n]);
		fprintf(write, "\n");
		n++;	
	}
	fclose(write);
	fclose(fp);

//	printf("[DEBUG]N: %d\n", n); 

	FILE * fin = popen("./stemmer < po_out","r");      // Nomalization

	while(!feof(fin)){
                fscanf(fin,"%s", buf);                
                printf("[DEBUG]BUF: %s\n", buf);
		strcpy(word[index], buf);
                printf("[DEBUG]After Stemmer[index%d]: %s\n", index, word[index]);
                printf("%s\n", word[index]);
		index+=1;
        }

	printf("[DEBUG]index: %d\n", index);

	printf("word[%d]: %s\n", 1, word[1]);
	printf("word[%d]: %s\n", 35, word[34]);
	printf("word[%d]: %s\n", 467, word[466]);

	b_Sort(word, index);

	for(int i=0; i<index; i++){		
//                printf("[DEBUG]After Sort: %s\n", word[i]);
	}


//	FILE * fp = fopen("po", "r");

	return 0;
}
