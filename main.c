/*
Programa de demonstracao de analise nodal modificada
Por Antonio Carlos M. de Queiroz acmq@coe.ufrj.br
Versao 1.0 - 6/9/2000
Versao 1.0a - 8/9/2000 Ignora comentarios
Versao 1.0b - 15/9/2000 Aumentado Yn, retirado Js
Versao 1.0c - 19/2/2001 Mais comentarios
Versao 1.0d - 16/2/2003 Tratamento correto de nomes em minusculas
Versao 1.0e - 21/8/2008 Estampas sempre somam. Ignora a primeira linha
Versao 1.0f - 21/6/2009 Corrigidos limites de alocacao de Yn
Versao 1.0g - 15/10/2009 Le as linhas inteiras
Versao 1.0h - 18/6/2011 Estampas correspondendo a modelos
 */

/*
Elementos aceitos e linhas do netlist:

Resistor:  R<nome> <no+> <no-> <resistencia>
VCCS:      G<nome> <io+> <io-> <vi+> <vi-> <transcondutancia>
VCVC:      E<nome> <vo+> <vo-> <vi+> <vi-> <ganho de tensao>
CCCS:      F<nome> <io+> <io-> <ii+> <ii-> <ganho de corrente>
CCVS:      H<nome> <vo+> <vo-> <ii+> <ii-> <transresistencia>
Fonte I:   I<nome> <io+> <io-> <corrente>
Fonte V:   V<nome> <vo+> <vo-> <tensao>
Amp. op.:  O<nome> <vo1> <vo2> <vi1> <vi2>

As fontes F e H tem o ramo de entrada em curto
O amplificador operacional ideal tem a saida suspensa
Os nos podem ser nomes
 */

#define versao "1.0h - 18/6/2011"
#include <stdio.h>

//Include especifico para Windows
#ifdef _WINDOWS
#include <conio.h>
#endif

#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <math.h>
#include <complex.h>
#define MAX_LINHA 80
#define MAX_STR_LEN 80
#define MAX_LINHA_EST 40
#define MAX_NOME 11
#define MAX_ELEM 50
#define MAX_NOS 50
#define TOLG 1e-9
#define DEBUG true
#define ABERTO 1e9
#define CURTO 1e-9
//#define USE_HAMONICS

typedef struct elemento { /* Elemento do netlist */
	char nome[MAX_NOME];
	char tipo[MAX_NOME];
	double complex valor;
	double ic;
	double param1;
	double param2;
	double param3;
	double param4;
	double param5;
	double param6;
	double param7;
	int a,b,c,d,x,y,netlistIndex;
} elemento;

elemento netlist[MAX_ELEM], *fontes[MAX_ELEM]; /* Netlist */

int
ne, /* Elementos */
nv, /* Variaveis */
nn, /* Nos */
indiceFontes;

unsigned maxHarmonicos=15;

int
i, j, k;

double
t,
tempoFinal,
passo,
u,v,w = 0;

char
/* Foram colocados limites nos formatos de leitura para alguma protecao
contra excesso de caracteres nestas variaveis */
nomearquivo[MAX_LINHA+1],
tipo,
na[MAX_NOME],nb[MAX_NOME],nc[MAX_NOME],nd[MAX_NOME],
lista[MAX_NOS+1][MAX_NOME+2], /*Tem que caber jx antes do nome */
txt[MAX_LINHA+1],
netlistParams[MAX_STR_LEN+1][MAX_LINHA_EST],
linhaAux[MAX_STR_LEN+1],
modelo[11],
* token = NULL,
*p;
FILE *arquivo;

double complex g;
double Yn[MAX_NOS+1][MAX_NOS+2], Yt[MAX_NOS+1][MAX_NOS+2];

long unsigned contadorPassos =0 ;

/* Resolucao de sistema de equacoes lineares.
Metodo de Gauss-Jordan com condensacao pivotal */
void resolversistema(void)
{
	int i,j,l, a;
	double complex t, p;

	for (i=1; i<=nv; i++) {
		t=0.0;
		a=i;
		for (l=i; l<=nv; l++) {
			if (fabs(Yn[l][i])>fabs(t)) {
				a=l;
				t=Yn[l][i];
			}
		}
		if (i!=a) {
			for (l=1; l<=nv+1; l++) {
				p=Yn[i][l];
				Yn[i][l]=Yn[a][l];
				Yn[a][l]=p;
			}
		}
		if (fabs(t)<TOLG) {
			printf("Sistema singular\n");
			exit(1);
		}
		for (j=nv+1; j>i; j--) {  /* Ponha j>0 em vez de j>i para melhor visualizacao */
			Yn[i][j] /= t;
			p=Yn[i][j];
			for (l=1; l<=nv; l++) {
				if (l!=i)
					Yn[l][j]-=Yn[l][i]*p;
			}
		}
	}
}

/* Rotina que conta os nos e atribui numeros a eles */
int numero(char *nome)
{
	int i,achou;

	i=0; achou=0;
	while (!achou && i<=nv)
		if (!(achou=!strcmp(nome,lista[i]))) i++;
	if (!achou) {
		if (nv==MAX_NOS) {
			printf("O programa so aceita ate %d nos\n",nv);
			exit(1);
		}
		nv++;
		strcpy(lista[nv],nome);
		return nv; /* novo no */
	}
	else {
		return i; /* no ja conhecido */
	}
}

// Retorna o harmonico de numero index de uma fonte
// retorna 0 se nao houver mais harmonicos
elemento* getHarmonic(elemento *fonte,int index) {
	printf("getHamonic: %p %i \n",fonte,index);
	if (fonte == 0)
		return 0;
	printf("getHamonic: %p %i %s tipo=%s\n",fonte,index,(*fonte).nome,(*fonte).tipo);
	// Esse elemento deve ser liberado no fim de cada analise de cada harmonico
	// Caso essa funcao retorne 0, ela mesmo vai liberar o elemento criado.
	elemento* ret = malloc(sizeof(elemento));
	// Configurando valores iniciais
	strcpy((*ret).nome,(*fonte).nome);
	strcpy((*ret).tipo,(*fonte).tipo);
	(*ret).a = (*fonte).a;
	(*ret).b = (*fonte).b;
	(*ret).c = (*fonte).c;
	(*ret).d = (*fonte).d;
	(*ret).netlistIndex = (*fonte).netlistIndex;
	(*ret).x = (*fonte).x;
	(*ret).y = (*fonte).y;
	(*ret).valor = 0;
	(*ret).param1 = 0;
	(*ret).param2 = 0;
	(*ret).param3 = 0;
	(*ret).param5 = 0;
	printf("Y U NO WORK %i %i\n",strcmp((*fonte).tipo,"DC"),index==0);
	if (strcmp((*fonte).tipo,"DC") == 0){
		if (index == 0){
			printf("Atualizando valor do harmonico para %f\n",creal((*fonte).valor));
			(*ret).valor = (*fonte).valor;
			return ret;
		}else {
			free(ret);
			return 0;
		}
	} else if (strcmp((*fonte).tipo,"SIN") == 0) {
		if (index > 1) {
			free(ret);
			return 0;
		}
		if (index == 0) {
			(*ret).valor = (*fonte).valor;
		} else if(index == 1) {
			(*ret).param1 = (*fonte).param1;
			(*ret).param2 = (*fonte).param2;
			(*ret).param3 = (*fonte).param3;
			(*ret).param4 = (*fonte).param4;
		}
		return ret;
	} else if (strcmp((*fonte).tipo,"PULSE") == 0) {

	} else {
		// tipo de fonte nao identificado
		free(ret);
		return 0;
	}
	return ret;
}

int main(void)
{
	setvbuf(stdout, NULL, _IONBF, 0);
	setvbuf(stderr, NULL, _IONBF, 0);
	unsigned indice,indiceHarmonicos;
	//clrscr();
	printf("Programa demonstrativo de analise nodal modificada\n");
	printf("Por Antonio Carlos M. de Queiroz - acmq@coe.ufrj.br\n");
	printf("Versao %s\n",versao);
	denovo:
	/* Leitura do netlist */
	ne=0; nv=0; indiceFontes=0; strcpy(lista[0],"0");
	printf("Nome do arquivo com o netlist (ex: mna.net): ");
	scanf("%50s",nomearquivo);
	arquivo=fopen(nomearquivo,"r");
	if (arquivo==0) {
		printf("Arquivo %s inexistente\n",nomearquivo);
		goto denovo;
	}
	printf("Lendo netlist:\n");
	fgets(txt,MAX_LINHA,arquivo);
	printf("Titulo: %s",txt);
	while (fgets(txt,MAX_LINHA,arquivo)) {
		ne++; /* Nao usa o netlist[0] */
		if (ne>MAX_ELEM) {
			printf("O programa so aceita ate %d elementos\n",MAX_ELEM);
			exit(1);
		}

		txt[0]=toupper(txt[0]);
		tipo=txt[0];
		//sscanf(txt,"%10s",netlist[ne].nome);
		//p=txt+strlen(netlist[ne].nome); /* Inicio dos parametros */
		printf("Linha atual: %s\n",txt);
		printf("Tipo: %c\n",tipo);
		/* O que e lido depende do tipo */
		if (tipo=='*') { /* Comentario comeca com "*" */
			printf("Comentario: %s",txt);
			ne--;
		}
		else {
			printf("Parseando linha\n");
			indice=0;
			token=strtok(txt," ()'\n'");
			printf("TOKEN: %s\n",token);
			while (token)
			{
				strcpy(netlistParams[indice],token);
				printf("Indice: %i - netlistParams[%i] = %s\n",indice,indice,netlistParams[indice]);
				token = strtok(NULL," ()'\n'");
				printf("NEXT TOKEN: %s\n",token);
				indice++;
			}
			strcpy(netlist[ne].nome,netlistParams[0]);
			printf("Nome: %s\n",netlist[ne].nome);
			// Esse tipo sera substituido em fontes V e I pelo tipo da fonte (DC, SIN, PULSE).
			// No restante dos casos, o tipo sera o identificador do elemento, como R, L, C, G, ...
			netlist[ne].tipo[0] = tipo;
			netlist[ne].netlistIndex = ne;
			if (tipo=='R') {
				printf("Tipo == R\n");
				netlist[ne].a=numero(netlistParams[1]);
				printf("A: %i\n",netlist[ne].a);
				netlist[ne].b=numero(netlistParams[2]);
				printf("B: %i\n",netlist[ne].b);
				netlist[ne].valor=atof(netlistParams[3]);
				printf("%s %i %i %g\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,creal(netlist[ne].valor));
			}
			else if (tipo=='I' || tipo == 'V'){
				if (indice<4) {
					printf("Numero de parametros incorreto para a Fonte %s\n", netlistParams[0]);
#ifdef _WINDOWS
					getch();
#endif
					exit(1);
				}
				strcpy(netlist[ne].nome,netlistParams[0]);
				netlist[ne].a=numero(netlistParams[1]);
				netlist[ne].b=numero(netlistParams[2]);
				strcpy(modelo,netlistParams[3]);

				if ((strcmp(modelo,"DC")==0)||(strcmp(modelo,"dc")==0)||(strcmp(modelo,"Dc")==0))
				{
					strcpy(netlist[ne].tipo,"DC");
					netlist[ne].valor=atof(netlistParams[4]);
					printf("%s %i %i %s %g\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].tipo,creal(netlist[ne].valor));
				}
				else if (strcmp(modelo,"SIN")==0)
				{
					strcpy(netlist[ne].tipo,"SIN");
					netlist[ne].valor=atof(netlistParams[4]);
					netlist[ne].param1=atof(netlistParams[5]);
					netlist[ne].param2=atof(netlistParams[6]);
					netlist[ne].param3=atof(netlistParams[7]);
					netlist[ne].param4=atof(netlistParams[8]);
					netlist[ne].param5=atof(netlistParams[9]);
					netlist[ne].param6=atof(netlistParams[10]);
					printf("%s %i %i %s(%g %g %g %g %g %g %g)\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].tipo,creal(netlist[ne].valor)
							,netlist[ne].param1,netlist[ne].param2,netlist[ne].param3,netlist[ne].param4,netlist[ne].param5,netlist[ne].param6);
				}
				else if (strcmp(modelo,"PULSE")==0)
				{
					strcpy(netlist[ne].tipo,"PULSE");
					netlist[ne].valor=atof(netlistParams[4]);
					netlist[ne].param1=atof(netlistParams[5]);
					netlist[ne].param2=atof(netlistParams[6]);
					netlist[ne].param3=atof(netlistParams[7]);
					netlist[ne].param4=atof(netlistParams[8]);
					netlist[ne].param5=atof(netlistParams[9]);
					netlist[ne].param6=atof(netlistParams[10]);
					netlist[ne].param7=atof(netlistParams[11]);
					printf("%s %i %i %s(%g %g %g %g %g %g %g %g)\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].tipo,netlist[ne].valor,netlist[ne].param1,netlist[ne].param2
							,netlist[ne].param3,netlist[ne].param4,netlist[ne].param5,netlist[ne].param6,netlist[ne].param7);
				}
				else
				{
					printf("Tipo de Fonte nao reconhecido: %s\n",modelo);
#ifdef _WINDOWS
					getch();
#endif
					exit(1);
				}

				fontes[indiceFontes] = &netlist[ne];
				indiceFontes++;
			}
			else if (tipo=='C' || tipo=='L'){
				//			sscanf(p,"%10s%10s%lg",na,nb,&netlist[ne].valor);
				netlist[ne].a=numero(netlistParams[1]);
				netlist[ne].b=numero(netlistParams[2]);
				netlist[ne].valor=atof(netlistParams[3]);
				netlist[ne].ic = 0;
				printf("%s %i %i %g\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].valor);
			}
			else if (tipo=='G' || tipo=='E' || tipo=='F' || tipo=='H') {
				//		  sscanf(p,"%10s%10s%10s%10s%lg",na,nb,nc,nd,&netlist[ne].valor);
				netlist[ne].a=numero(netlistParams[1]);
				netlist[ne].b=numero(netlistParams[2]);
				netlist[ne].c=numero(netlistParams[3]);
				netlist[ne].d=numero(netlistParams[4]);
				netlist[ne].valor = atof(netlistParams[5]);
				printf("%s %i %i %i %i %g\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].c,netlist[ne].d,netlist[ne].valor);
			}
			else if (tipo=='O') {
				//		  sscanf(p,"%10s%10s%10s%10s",na,nb,nc,nd);
				netlist[ne].a=numero(netlistParams[1]);
				netlist[ne].b=numero(netlistParams[2]);
				netlist[ne].c=numero(netlistParams[3]);
				netlist[ne].d=numero(netlistParams[4]);
				printf("%s %i %i %i %i\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].c,netlist[ne].d);
			}
			else if (tipo == '.'){
				//sscanf(p,"%d %d",tempoFinal,passo);
				tempoFinal = atof(netlistParams[1]);
				passo = atof(netlistParams[2]);
				printf("Tempo Final: %f ; Passo: %f\n",tempoFinal,passo);
			}
			else {
				printf("Elemento desconhecido: %s\n",txt);
#ifdef _WINDOWS
				getch();
#endif
				exit(1);
			}
		}
	}
	fclose(arquivo);
	/* Acrescenta variaveis de corrente acima dos nos, anotando no netlist */
	nn=nv;
	for (i=1; i<=ne; i++) {
		tipo=netlist[i].nome[0];
		if (tipo=='V' || tipo=='E' || tipo=='F' || tipo=='O') {
			nv++;
			if (nv>MAX_NOS) {
				printf("As correntes extra excederam o numero de variaveis permitido (%d)\n",MAX_NOS);
				exit(1);
			}
			strcpy(lista[nv],"j"); /* Tem espaco para mais dois caracteres */
			strcat(lista[nv],netlist[i].nome);
			netlist[i].x=nv;
		}
		else if (tipo=='H') {
			nv=nv+2;
			if (nv>MAX_NOS) {
				printf("As correntes extra excederam o numero de variaveis permitido (%d)\n",MAX_NOS);
				exit(1);
			}
			strcpy(lista[nv-1],"jx"); strcat(lista[nv-1],netlist[i].nome);
			netlist[i].x=nv-1;
			strcpy(lista[nv],"jy"); strcat(lista[nv],netlist[i].nome);
			netlist[i].y=nv;
		}
	}
#ifdef _WINDOWS
	getch();
#endif
	/* Lista tudo */
	printf("Variaveis internas: \n");
	for (i=0; i<=nv; i++)
		printf("%d -> %s\n",i,lista[i]);
#ifdef _WINDOWS
	getch();
#endif
	printf("Netlist interno final\n");
	for (i=1; i<=ne; i++) {
		tipo=netlist[i].nome[0];
		if (tipo=='R' || tipo=='I' || tipo=='V') {
			printf("%s %d %d %g\n",netlist[i].nome,netlist[i].a,netlist[i].b,netlist[i].valor);
		}
		else if (tipo=='G' || tipo=='E' || tipo=='F' || tipo=='H') {
			printf("%s %d %d %d %d %g\n",netlist[i].nome,netlist[i].a,netlist[i].b,netlist[i].c,netlist[i].d,netlist[i].valor);
		}
		else if (tipo=='O') {
			printf("%s %d %d %d %d\n",netlist[i].nome,netlist[i].a,netlist[i].b,netlist[i].c,netlist[i].d);
		}
		if (tipo=='V' || tipo=='E' || tipo=='F' || tipo=='O')
			printf("Corrente jx: %d\n",netlist[i].x);
		else if (tipo=='H')
			printf("Correntes jx e jy: %d, %d\n",netlist[i].x,netlist[i].y);
	}
#ifdef _WINDOWS
	getch();
#endif
	/* Monta o sistema nodal modificado */
	printf("O circuito tem %d nos, %d variaveis e %d elementos\n",nn,nv,ne);
#ifdef _WINDOWS
	getch();
#endif
	/* Zera sistema */

	t=0;

	do
	{

		printf("Iniciando varredura de tempo\nZerando sistema nodal\n");
		for(i=0;i<=nv;i++){
			for(j=0;j<=nv+1;j++) {
				printf("Zerando item Yt[%i][%i]\n",i,j);
				Yt[i][j] = 0;
			}
		}

		elemento *fonte;
		int indiceFonte = 0;
		printf("Indice FONTES: %i\n",indiceFontes);
		for (k=0;k<indiceFontes;k++) {
			printf("Varrendo fontes %i %p %s\n",k,fontes[k],(*fontes[k]).nome);
#ifdef USE_HARMONICS
			for(indiceHarmonicos=0;indiceHarmonicos<maxHarmonicos;indiceHarmonicos++) {
				fonte=getHarmonic(fontes[k],indiceHarmonicos);
#else
				fonte=fontes[k];
#endif
				indiceFonte = (*fontes[k]).netlistIndex;
				if (fonte==0) {
					printf("Nao ha mais harmonicos para essa fonte\n");
				}else {
					for (i=0; i<=nv; i++) {
						for (j=0; j<=nv+1; j++)
							Yn[i][j]=0;
					}
					printf("Montando estampas: ne=%i\n",ne);
					/* Monta estampas */
					for (i=1; i<=ne; i++) {
						tipo=netlist[i].nome[0];
						if (tipo == 'V' && ! i == indiceFonte) {
							printf("Adicionando fonte 0\n");
							Yn[netlist[k].a][netlist[i].x]+=1;
							Yn[netlist[k].b][netlist[i].x]-=1;
							Yn[netlist[k].x][netlist[i].a]-=1;
							Yn[netlist[k].x][netlist[i].b]+=1;
							Yn[netlist[k].x][nv+1]-=0;
						} else if (tipo == 'I'){
							// do nothing
						}
						else if (tipo=='R') {
							g=1/netlist[i].valor;
							Yn[netlist[i].a][netlist[i].a]+=g;
							Yn[netlist[i].b][netlist[i].b]+=g;
							Yn[netlist[i].a][netlist[i].b]-=g;
							Yn[netlist[i].b][netlist[i].a]-=g;
						}

						else if (tipo=='C'){

							printf("Frequencia da fonte: %f PI=%f I^2=%i\n",(*fonte).param2,M_PI,I*I);

							if ((*fonte).param2 == 0)
								g = 1/ABERTO;
							else
								g=cabsf(I * (*fonte).param2*2*M_PI * netlist[i].valor);

							//printf("Capacitor - impedancia=%f + j%f\n",creal(g),cimag(g));
							Yn[netlist[i].a][netlist[i].a]+=g;
							Yn[netlist[i].b][netlist[i].b]+=g;
							Yn[netlist[i].a][netlist[i].b]-=g;
							Yn[netlist[i].b][netlist[i].a]-=g;
						}
						else if(tipo=='L'){
							if ((*fonte).param2 == 0)
								g=cabsf(1/(I * (*fonte).param2*2*M_PI * netlist[i].valor));
							else
								g=1/CURTO;
							Yn[netlist[i].a][netlist[i].a]+=g;
							Yn[netlist[i].b][netlist[i].b]+=g;
							Yn[netlist[i].a][netlist[i].b]-=g;
							Yn[netlist[i].b][netlist[i].a]-=g;
						}
						else if (tipo=='G') {
							g=netlist[i].valor;
							Yn[netlist[i].a][netlist[i].c]+=g;
							Yn[netlist[i].b][netlist[i].d]+=g;
							Yn[netlist[i].a][netlist[i].d]-=g;
							Yn[netlist[i].b][netlist[i].c]-=g;
						}
						else if (tipo=='E') {
							g=netlist[i].valor;
							Yn[netlist[i].a][netlist[i].x]+=1;
							Yn[netlist[i].b][netlist[i].x]-=1;
							Yn[netlist[i].x][netlist[i].a]-=1;
							Yn[netlist[i].x][netlist[i].b]+=1;
							Yn[netlist[i].x][netlist[i].c]+=g;
							Yn[netlist[i].x][netlist[i].d]-=g;
						}
						else if (tipo=='F') {
							g=netlist[i].valor;
							Yn[netlist[i].a][netlist[i].x]+=g;
							Yn[netlist[i].b][netlist[i].x]-=g;
							Yn[netlist[i].c][netlist[i].x]+=1;
							Yn[netlist[i].d][netlist[i].x]-=1;
							Yn[netlist[i].x][netlist[i].c]-=1;
							Yn[netlist[i].x][netlist[i].d]+=1;
						}
						else if (tipo=='H') {
							g=netlist[i].valor;
							Yn[netlist[i].a][netlist[i].y]+=1;
							Yn[netlist[i].b][netlist[i].y]-=1;
							Yn[netlist[i].c][netlist[i].x]+=1;
							Yn[netlist[i].d][netlist[i].x]-=1;
							Yn[netlist[i].y][netlist[i].a]-=1;
							Yn[netlist[i].y][netlist[i].b]+=1;
							Yn[netlist[i].x][netlist[i].c]-=1;
							Yn[netlist[i].x][netlist[i].d]+=1;
							Yn[netlist[i].y][netlist[i].x]+=g;
						}
						else if (tipo=='O') {
							Yn[netlist[i].a][netlist[i].x]+=1;
							Yn[netlist[i].b][netlist[i].x]-=1;
							Yn[netlist[i].x][netlist[i].c]+=1;
							Yn[netlist[i].x][netlist[i].d]-=1;
						}
					}
					printf("3 fontes[k]=%p\n",fontes[k]);

					if ((*fonte).nome[0] =='I') {
						if (strcmp((*fonte).tipo,"DC") == 0) {
							g=(*fonte).valor;
						} else if (strcmp((*fonte).tipo,"SIN") == 0) {
							g=(*fonte).valor + (*fonte).param1*sin(t*(*fonte).param2 + (*fonte).param5);
						} else if (strcmp((*fonte).tipo,"PULSE") == 0) {

						}
						Yn[(*fonte).a][nv+1]-=g;
						Yn[(*fonte).b][nv+1]+=g;
					}
					else if ((*fonte).nome[0] == 'V') {
						printf("Adicionando fonte de tensao TIPO=%s\n",(*fonte).tipo);
						Yn[(*fonte).a][(*fonte).x] += 1;
						Yn[(*fonte).b][(*fonte).x] -= 1;
						Yn[(*fonte).x][(*fonte).a] -= 1;
						Yn[(*fonte).x][(*fonte).b] += 1;
						printf("VERIFICANDO TIPO DA FONTE\n");
						if (strcmp((*fonte).tipo,"DC") == 0) {
							printf("VALOR DA FONTE: %f\n",creal((*fonte).valor));
							Yn[(*fonte).x][nv+1] -= (*fonte).valor;
						} else if(strcmp((*fonte).tipo,"SIN") == 0) {
							printf("Adicionando fonte senoidal com\n\tDC=%f\n\tamplitude=%f\n\tfrequencia=%f\n\tfase=%f\n",creal((*fonte).valor),creal((*fonte).param1),creal((*fonte).param2),creal((*fonte).param5));
							printf("Argmento do seno: %f rad, %f ang\n",t*(*fonte).param2*2*M_PI,t*(*fonte).param2);
							printf("sin(90)=%f,sin(pi)=%f,sin(90*pi/180)=%f\n",sin(90),sin(M_PI),sin(90*M_PI/180));
							Yn[(*fonte).x][nv+1] -= (*fonte).valor + ((*fonte).param1)*sin((t*(*fonte).param2)*M_PI/180 + (*fonte).param5);
							printf("Valor da fonte: %f\n",Yn[(*fonte).x][nv+1]);
						} else if (strcmp((*fonte).tipo,"PULSE") == 0) {

						} else {
							printf("TIPO DA FONTE NAO IDENTIFICADO\n");
						}
					}
					/* Opcional: Mostra o sistema apos a montagem da estampa */
					//	printf("Sistema apos a estampa de %s\n",netlist[i].nome);
					for (i=1; i<=nv; i++) {
						for (j=1; j<=nv+1; j++)
							if (Yn[i][j]!=0)
								printf("%+3.1f ",Yn[i][j]);
							else
								printf(" ... ");
						printf("\n");
					}
#ifdef _WINDOWS
					getch();
#endif
					printf("\n\nResolvendo o sistema\n\n");
					/* Resolve o sistema */
					printf("4 fontes[k]=%p\n",fontes[k]);
					resolversistema();
					printf("\n\nCopiando a solucaoão para Yt nv=%i\n\n",nv);
					printf("5 fontes[k]=%p\n",fontes[k]);

					/* Opcional: Mostra o sistema resolvido */
					printf("Sistema resolvido:\n");
					for (i=1; i<=nv; i++) {
						for (j=1; j<=nv+1; j++) {
//							printf("ADDIND Yn[%i][%i]=%f to Yt[%i][%i]=%f\n",i,j,creal(Yn[i][j]),i,j,creal(Yt[i][j]));
							Yt[i][j] += Yn[i][j];
//							printf("Novo Yt[%i][%i]=%f\n",i,j,creal(Yt[i][j]));
							//	#ifdef DEBUG
							if (Yn[i][j]!=0)
								printf("%+3.1f ",creal(Yn[i][j]));
							else
								printf(" ... ");
							//	#endif
						}
						printf("\n");
					}
#ifdef _WINDOWS
					getch();
#endif
#ifdef USE_HARMONICS
					printf("Liberando harmonico %i da fonte\n",indiceHarmonicos);
					printf("fontes[k]=%p\n",fontes[k]);
					free(fonte);
					printf("Liberado! fontes[k]=%p\n",fontes[k]);
				}

				printf("Pegando proximo harmonico %i da fonte %i\n",indiceHarmonicos+1,k);
#endif
			}
#ifdef USE_HARMONICS
			printf("Finalizado analisando harmonicos da fonte indice %i\n",k);
#endif
		}
		/* Mostra solucao */
		printf("Solucao:\n");
		strcpy(txt,"Tensao");
		for (i=1; i<=nv; i++) {
			if (i==nn+1)
				strcpy(txt,"Corrente");
			printf("%s %s: %g\n",txt,lista[i],creal(Yt[i][nv+1]));
		}
		/* Salva solucao */
		//		if (t==0)
		//			passo=(passo*1000.0);

//		if (contadorDePassos==0){
//			fprintf(arquivo,"%.15f ",t);
//			for (i=1; i<=nv; i++) {
//				fprintf(arquivo,"%.15f ",Yn[i][nv+1]);
//			}
//			fprintf(arquivo,"\n");
//		}

		printf("Tempo atual: %f\n",t);
		printf("Passo: %f\n",passo);
		t = t + passo;
		printf("Tempo + passo: %f\n",t);
		printf("Tempo Final: %f\n",tempoFinal);
		contadorPassos++;
#ifdef _WINDOWS
		getch();
#endif
	}while(t<tempoFinal);

	return 0;
}

