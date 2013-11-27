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

/*
Versão 1.1
Resolve circuitos no estado permanente senoidal.
Baseado no programa original fornecido pelo professor Antonio Carlos Moreirão.
Por David E. de Britto Junior.

Novos elementos aceitos no netlist:
Capacitor: C<nome> <no+> <no-> <capacitancia>
Indutor: L<nome> <no+> <no-> <indutancia>
Transformador: K<nome> <L1> <L2> <acoplamento>

Fontes Independentes (Corrente ou tensão):
DC <valor>
SIN <nivel contínuo> <amplitude> <frequência (Hz)> <atraso*> <atenuação*> <ângulo> <número de ciclos*>
 */

// Debug deve ser definido durante a compilacao
//#define DEBUG true
#define versao "1.1 - 22/11/2013"
#include <stdio.h>

//Include especifico para Windows
#if defined(_WIN32)
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
#define ABERTO 1e9
#define CURTO 1e-9
#define MAX_HARMONIC_LIMIT 200

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

elemento netlist[MAX_ELEM], *fontes[MAX_ELEM], *indutores[MAX_ELEM], *transformadores[MAX_ELEM][3]; /* Netlist */

int
ne, /* Elementos */
nv, /* Variaveis */
nn, /* Nos */

// Contadores do numero de fontes de tensão, indutores e transformadores
indiceFontes,
indiceIndutores=0,
indiceTransformadores=0,
repeatHarmonic = 0;

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
outputFilename[MAX_LINHA+1],
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

double Yt[MAX_NOS+1][MAX_NOS+2];
double complex g;
double complex Yn[MAX_NOS+1][MAX_NOS+2];

/* Resolucao de sistema de equacoes lineares.
Metodo de Gauss-Jordan com condensacao pivotal */
int resolversistema(void)
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
#ifdef DEBUG
			printf("Sistema singular\n");
#endif
			return 1;
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
	return 0;
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
	if (fonte == 0)
		return 0;

	// Esse elemento deve ser liberado no fim de cada analise de cada harmonico
	// Caso essa funcao retorne 0, ela mesmo vai liberar o elemento criado.
	elemento* ret = malloc(sizeof(elemento));
	// Configurando valores iniciais
	strcpy(ret->nome,fonte->nome);
	strcpy(ret->tipo,fonte->tipo);
	ret->a = fonte->a;
	ret->b = fonte->b;
	ret->c = fonte->c;
	ret->d = fonte->d;
	ret->netlistIndex = fonte->netlistIndex;
	ret->x = fonte->x;
	ret->y = fonte->y;
	ret->valor = 0;
	ret->param1 = 0;
	ret->param2 = 0;
	ret->param3 = 0;
	ret->param5 = 0;
	ret->param6 = fonte->param6;
	ret->param7 = 0;

	if (strcmp(fonte->tipo,"DC") == 0){
		if (index == 0){
			ret->valor = fonte->valor;
			return ret;
		}else {
			free(ret);
			return 0;
		}
	} else if (strcmp(fonte->tipo,"SIN") == 0) {
		if (index == 0) {
			ret->valor = fonte->valor;
			strcpy(ret->tipo,"DC");
		} else if(index == 1) {
			ret->param1 = fonte->param1;
			ret->param2 = fonte->param2;
			ret->param3 = fonte->param3;
			ret->param4 = fonte->param4;
		} else {
			free(ret);
			return 0;
		}
		return ret;
	} else if (strcmp(fonte->tipo,"PULSE") == 0) {
		/*
		 	netlist[ne].valor=atof(netlistParams[4]);   // amp 1
			netlist[ne].param1=atof(netlistParams[5]);  // amp 2
			netlist[ne].param2=atof(netlistParams[6]);  // atraso
			netlist[ne].param3=atof(netlistParams[7]);  // tempo subida
			netlist[ne].param4=atof(netlistParams[8]);  // tempo descida
			netlist[ne].param5=atof(netlistParams[9]);  // tempo ligado
			netlist[ne].param6=atof(netlistParams[10]); // periodo
			netlist[ne].param7=atof(netlistParams[11]); // nao utilizado
		 */

		double max = fonte->param1;
		double min = fonte->valor;
		double atraso = fonte->param2;
		double tRise = fonte->param3;
		double tFall = fonte->param4;
		double tOn = fonte->param5;
		double period = fonte->param6;
		double tOff = period - (tRise + tOn + tFall);

		if (index == 0) {
			//ret->valor = 1/fonte->param6 * (fonte->valor * tOff + (fonte->param1 - fonte->valor)*(fonte->param3 + 2*tOff)/2 + fonte->valor*fonte->param3 - tOff*(fonte->param1 - fonte->valor) + fonte->param1*fonte->param5 + (fonte->valor + fonte->param1)*fonte->param4/2);
			ret->valor = (max + min)/2;
			strcpy(ret->tipo,"DC");
			return ret;
		} else {
			printf("Calculando harmonico %i da fonte %s\n",index,fonte->nome);
			double w = 2*M_PI*index/period;
			double t1 = tRise;
			double t2 = tRise + tOn;
			double t3 = tRise + tOn + tFall;
			double t4 = period;
			printf("w=%g\nt1=%g\nt2=%g\nt3=%g\nt4=%g\n",w,t1,t2,t3,t4);
			double a = (max-min)/(t2-t3);
			double b = (min*t2 - max*t3)/(t2-t3);
			printf("A=%g\nB=%g\n",a,b);

			if (tRise ==0 && tFall == 0) {

				ret->valor = (2/period) * (max/w) * sin(w*tOn)
						   + (2/period) * (min/w) * (sin(w*period) -sin(w*tOn));

				ret->param1 = (2/period) * (min/w) * (1 - cos(w*tOn))
							+ (2/period) * (min/w) * (cos(w*tOn) - cos(w*period));

			} else {
				ret->valor = 2/period * pow((1/w),2) * (w*max*sin(w*t1) + ( (max-min)/t1 )*cos(w*t1) - (max-min)/t1 )
						   + 2/period * (1/w) * (max*sin(w*t2) - max*sin(w*t1))
						   + 2/period * pow((1/w),2) * ( w*(a*t3 +b)*sin(w*t3) - w*(a*t2 +b)*sin(w*t2) - a*cos(w*t2) + a*cos(w*t3) )
						   + 2/period *(1/w) * (min*sin(w*t4) - min*sin(w*t3));

				ret->param1 = 2/period * pow((1/w),2) * (-1*w*max*cos(w*t1) + ((max-min)/t1)*sin(w*t1) + min*w )
							+ 2/period * (1/w) * max * (cos(w*t1) - cos(w*t2))
							+ 2/period * pow((1/w),2) * (w*(a*t2+b)*cos(w*t2) - w*(a*t3 +b)*cos(w*t3) + a*sin(w*t3) - a*sin(w*t2) )
							+ 2/period * (1/w) * min * (cos(w*t3) - cos(w*t4));

			}
			printf("Valor=%g\n",ret->valor);
			printf("Param1=%g\n",ret->param1);
			//
//
//			double c1 = (fonte->param3) ? (fonte->param1 - fonte->valor) / fonte->param3 : 0;
//			double c2 = (fonte->param4) ? (fonte->valor - fonte->param1) / fonte->param4 : 0;
//			double k1 = (fonte->param3) ? fonte->valor - (fonte->param1 - fonte->valor) * tOff / fonte->param3 : fonte->valor;
//			double k2 = (fonte->param4) ? fonte->param1 - (fonte->valor - fonte->param1) * (fonte->param6 - fonte->param4) / fonte->param4 : fonte->param1;
//			ret->valor = fonte->valor / (M_PI * index) * sin(2 * M_PI * index * tOff / fonte->param6) +
//					(c1 / (M_PI * index) * (fonte->param6 / (2 * M_PI * index) * (cos(2 * M_PI * index *(tOff + fonte->param3) / fonte->param6) - cos(2 * M_PI * index * tOff / fonte->param6)) +
//							(tOff + fonte->param3) * sin(2 * M_PI * index * (tOff + fonte->param3) / fonte->param6) - tOff * sin(2 * M_PI * index * tOff / fonte->param6)) +
//							k1 / (M_PI * index) * (sin(2 * M_PI * index * (tOff + fonte->param3) / fonte->param6) - sin(2 * M_PI * index * tOff / fonte->param6))) +
//							fonte->param1 / (M_PI * index) * (sin(2 * M_PI * index * (fonte->param6 - fonte->param4) / fonte->param6) - sin(2 * M_PI * index * (tOff + fonte->param3) / fonte->param6)) +
//							(c2 / (M_PI * index) * (fonte->param6 / (2 * M_PI * index) * (cos(2 * M_PI * index) - cos(2 * M_PI * index * (fonte->param6 - fonte->param4) / fonte->param6)) +
//									fonte->param6 * sin(2 * M_PI * index) - (fonte->param6 - fonte->param4) * sin(2 * M_PI * index * (fonte->param6 - fonte->param4) / fonte->param6)) +
//									k2 / (M_PI * index) * (sin(2 * M_PI * index) - sin(2 * M_PI * index * (fonte->param6 - fonte->param4) / fonte->param6)));
//
//			ret->param1 = (fonte->valor / (M_PI * index) * (1 - cos(2 * M_PI * index * tOff / fonte->param6)) +
//					(c1 / (M_PI * index) * (fonte->param6 / (2 * M_PI * index) * (sin(2 * M_PI * index * (tOff + fonte->param3) / fonte->param6) - sin(2 * M_PI * index * tOff / fonte->param6)) +
//							tOff * cos(2 * M_PI * index * tOff / fonte->param6) - (tOff + fonte->param3) * cos(2 * M_PI * index * (tOff + fonte->param3) / fonte->param6)) +
//							k1 / (M_PI * index) * (cos(2 * M_PI * index	* tOff/ fonte->param6) - cos(2 * M_PI * index * (tOff + fonte->param3) / fonte->param6))) +
//							fonte->param1 / (M_PI * index) * (cos(2 * M_PI * index * (tOff + fonte->param3) / fonte->param6) - cos(2 * M_PI * index * (fonte->param6 - fonte->param4) / fonte->param6)) +
//							(c2 / (M_PI * index) * (fonte->param6 / (2 * M_PI * index) * (sin(2 * M_PI * index) - sin(2 * M_PI * index * (fonte->param6 - fonte->param4) / fonte->param6)) +
//									(fonte->param6 - fonte->param4) * cos(2 * M_PI * index * (fonte->param6 - fonte->param4) / fonte->param6) - fonte->param6 * cos(2 * M_PI * index)) +
//									k2 / (M_PI * index) * (cos(2 * M_PI * index * (fonte->param6 - fonte->param4) / fonte->param6) - cos(2 * M_PI * index))));

			ret->param2 = index/ret->param6;
			return ret;
		}
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
	printf("Adaptado por David E. de Britto Junior para resolver circuitos em estado permanente senoidal.");
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
	printf("Lendo netlist do arquivo: %s\n",nomearquivo);
	//Copiando o nome do arquivo de entrada sem a extensão de netlist ("net")
	strncpy(outputFilename,nomearquivo,strlen(nomearquivo)-3);
	//Adicionando a extensão tab ao nome do arquivo de saida
	strcat(outputFilename,"tab");
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
		//p=txt+strlen(netlist[ne].nome); /* Inicio dos parametros */
		/* O que e lido depende do tipo */
		if (tipo=='*') { /* Comentario comeca com "*" */
			printf("Comentario: %s",txt);
			ne--;
		}
		else {
			indice=0;
			token=strtok(txt," ()'\n'");
			while (token)
			{
				strcpy(netlistParams[indice],token);
				token = strtok(NULL," ()'\n'");
				indice++;
			}
			strcpy(netlist[ne].nome,netlistParams[0]);
#ifdef DEBUG
			printf("Elemento %s valores: ",netlist[ne].nome);
#endif
			// Esse tipo sera substituido em fontes V e I pelo tipo da fonte (DC, SIN, PULSE).
			// No restante dos casos, o tipo sera o identificador do elemento, como R, L, C, G, ...
			netlist[ne].tipo[0] = tipo;
			netlist[ne].netlistIndex = ne;
			if (tipo=='R') {
				netlist[ne].a=numero(netlistParams[1]);
				netlist[ne].b=numero(netlistParams[2]);
				netlist[ne].valor=atof(netlistParams[3]);
#ifdef DEBUG
				printf("%s %i %i %g\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,creal(netlist[ne].valor));
#endif
			}
			else if (tipo=='I' || tipo == 'V'){
				if (indice<4) {
					printf("Numero de parametros incorreto para a Fonte %s\n", netlistParams[0]);
#if defined(_WIN32) && defined(DEBUG)
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
#ifdef DEBUG
					printf("%s %i %i %s %g\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].tipo,creal(netlist[ne].valor));
#endif
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
#ifdef DEBUG
					printf("%s %i %i %s(%g %g %g %g %g %g %g)\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].tipo,creal(netlist[ne].valor)
							,netlist[ne].param1,netlist[ne].param2,netlist[ne].param3,netlist[ne].param4,netlist[ne].param5,netlist[ne].param6);
#endif
				}

				else if (strcmp(modelo,"PULSE")==0)
				{
					strcpy(netlist[ne].tipo,"PULSE");
					netlist[ne].valor=atof(netlistParams[4]);   // amp 1
					netlist[ne].param1=atof(netlistParams[5]);  // amp 2
					netlist[ne].param2=atof(netlistParams[6]);  // atraso
					netlist[ne].param3=atof(netlistParams[7]);  // tempo subida
					netlist[ne].param4=atof(netlistParams[8]);  // tempo descida
					netlist[ne].param5=atof(netlistParams[9]);  // tempo ligado
					netlist[ne].param6=atof(netlistParams[10]); // periodo
					netlist[ne].param7=atof(netlistParams[11]); // nao utilizado
#ifdef DEBUG
					printf("%s %i %i %s(%g %g %g %g %g %g %g %g)\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].tipo,netlist[ne].valor,netlist[ne].param1,netlist[ne].param2
							,netlist[ne].param3,netlist[ne].param4,netlist[ne].param5,netlist[ne].param6,netlist[ne].param7);
#endif
				}
				else
				{
					printf("Tipo de Fonte nao reconhecido: %s\n",modelo);
#if defined(_WIN32) && defined(DEBUG)
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

				if (tipo=='L') {
					indutores[indiceIndutores] = &netlist[ne];
					indiceIndutores++;
				}
#ifdef DEBUG
				printf("%s %i %i %g\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].valor);
#endif
			}
			else if (tipo=='K') {
				elemento *L1,*L2 = 0;
				for (i=0;i<indiceIndutores;i++) {
					if (L1 == 0 || L2 == 0) {
						if (strcmp(indutores[i]->nome,netlistParams[1]) == 0)
							L1 = indutores[i];
						else if (strcmp(indutores[i]->nome,netlistParams[2]) == 0)
							L2 = indutores[i];
					}
				}

				netlist[ne].valor = atof(netlistParams[3]) * sqrt(L1->valor * L2->valor);
				netlist[ne].param1 = indiceTransformadores;
				transformadores[indiceTransformadores][0] = &netlist[ne];
				transformadores[indiceTransformadores][1] = L1;
				transformadores[indiceTransformadores][2] = L2;
				indiceTransformadores++;
			}
			else if (tipo=='G' || tipo=='E' || tipo=='F' || tipo=='H') {
				//		  sscanf(p,"%10s%10s%10s%10s%lg",na,nb,nc,nd,&netlist[ne].valor);
				netlist[ne].a=numero(netlistParams[1]);
				netlist[ne].b=numero(netlistParams[2]);
				netlist[ne].c=numero(netlistParams[3]);
				netlist[ne].d=numero(netlistParams[4]);
				netlist[ne].valor = atof(netlistParams[5]);
#ifdef DEBUG
				printf("%s %i %i %i %i %g\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].c,netlist[ne].d,netlist[ne].valor);
#endif
			}
			else if (tipo=='O') {
				//		  sscanf(p,"%10s%10s%10s%10s",na,nb,nc,nd);
				netlist[ne].a=numero(netlistParams[1]);
				netlist[ne].b=numero(netlistParams[2]);
				netlist[ne].c=numero(netlistParams[3]);
				netlist[ne].d=numero(netlistParams[4]);
#ifdef DEBUG
				printf("%s %i %i %i %i\n",netlist[ne].nome,netlist[ne].a,netlist[ne].b,netlist[ne].c,netlist[ne].d);
#endif
			}
			else if (tipo == '.'){
				//sscanf(p,"%d %d",tempoFinal,passo);
				tempoFinal = atof(netlistParams[1]);
				passo = atof(netlistParams[2]);
				if (atoi(netlistParams[3])) {
					maxHarmonicos = atoi(netlistParams[3]);
				} else {
					maxHarmonicos = 1/passo;
					if (maxHarmonicos > MAX_HARMONIC_LIMIT)
						maxHarmonicos = MAX_HARMONIC_LIMIT;
				}
				printf("Tempo de simulacao: %g\nPasso=%g\nNumero de harmonicos=%i\n",tempoFinal,passo,maxHarmonicos);
			}
			else {
				printf("Elemento desconhecido: %s\n",txt);
#if defined(_WIN32) && defined(DEBUG)
				getch();
#endif
				exit(1);
			}

			//Limpando netlistParams:
			for (i=0;i<indice;i++){
				strcpy(netlistParams[i],"\0");
			}
		}
	}
	fclose(arquivo);
	/* Acrescenta variaveis de corrente acima dos nos, anotando no netlist */
	nn=nv;
	for (i=1; i<=ne; i++) {
		tipo=netlist[i].nome[0];
		if (tipo=='V' || tipo=='E' || tipo=='F' || tipo=='O' || tipo == 'L') {
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

	for (i=0;i<indiceTransformadores;i++){
		transformadores[i][0]->x = transformadores[i][1]->x;
		transformadores[i][0]->y = transformadores[i][2]->x;
	}
#ifdef DEBUG

#ifdef _WIN32
	getch();
#endif
	/* Lista tudo */
	printf("Variaveis internas: \n");
	for (i=0; i<=nv; i++)
		printf("%d -> %s\n",i,lista[i]);
#ifdef _WIN32
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
#ifdef _WIN32
	getch();
#endif
	/* Monta o sistema nodal modificado */

	printf("O circuito tem %d nos, %d variaveis e %d elementos\n",nn,nv,ne);


#ifdef _WIN32
	getch();
#endif

#endif
	/* Zera sistema */


	//lista[i]
	// Escrevendo header do arquivo
	FILE *outputFile;
	int count=1;
	outputFile = fopen(outputFilename,"w");
	fprintf(outputFile,"t");
	for (count=1; count<=nv; count++) {
		fprintf(outputFile," %s",lista[count]);
	}
	fprintf(outputFile,"\n");

	t=0;
#ifdef DEBUG
	printf("Iniciando analise no tempo\n");
#endif
	do
	{
		for(i=0;i<=nv;i++)
			for(j=0;j<=nv+1;j++)
				Yt[i][j] = 0;

		elemento *fonte;
		int indiceFonte = 0;
#ifdef DEBUG
		printf("Iniciando varredura de fontes\n");
#endif
		for (k=0;k<indiceFontes;k++) {
#ifdef DEBUG
			printf("Iniciando varredura de harmonicos para a fonte %s, tipo %s\n",fontes[k]->nome,fontes[k]->tipo);
#endif
			for(indiceHarmonicos=0;indiceHarmonicos<maxHarmonicos;indiceHarmonicos++) {
				fonte=getHarmonic(fontes[k],indiceHarmonicos);
				indiceFonte = fontes[k]->netlistIndex;
				if (fonte==0) {
#ifdef DEBUG
					printf("Nao ha mais harmonicos para essa fonte\n");
#endif
				}else {
#ifdef DEBUG
					printf("Montando matriz de analise nodal para o harmonico indice %i\n",indiceHarmonicos);
#endif
					for (i=0; i<=nv; i++) {
						for (j=0; j<=nv+1; j++)
							Yn[i][j]=0;
					}
					/* Monta estampas */
					for (i=1; i<=ne; i++) {
						tipo=netlist[i].nome[0];
						if (tipo == 'V' && i != indiceFonte) {
							Yn[netlist[i].a][netlist[i].x]+=1;
							Yn[netlist[i].b][netlist[i].x]-=1;
							Yn[netlist[i].x][netlist[i].a]-=1;
							Yn[netlist[i].x][netlist[i].b]+=1;
							Yn[netlist[i].x][nv+1]-=0;
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
							if (fonte->param2 == 0)
								g = 1/ABERTO;
							else
								g=I * fonte->param2*2*M_PI * netlist[i].valor;

							//printf("Capacitor - impedancia=%f + j%f\n",creal(g),cimag(g));
							Yn[netlist[i].a][netlist[i].a]+=g;
							Yn[netlist[i].b][netlist[i].b]+=g;
							Yn[netlist[i].a][netlist[i].b]-=g;
							Yn[netlist[i].b][netlist[i].a]-=g;
						}
						else if(tipo=='L'){
							if (fonte->param2 == 0)
								g=CURTO;
							else
								g=I * fonte->param2*2*M_PI * netlist[i].valor;

							Yn[netlist[i].a][netlist[i].x]+=1;
							Yn[netlist[i].b][netlist[i].x]-=1;
							Yn[netlist[i].x][netlist[i].a]-=1;
							Yn[netlist[i].x][netlist[i].b]+=1;
							Yn[netlist[i].x][netlist[i].x]+=g;
						}
						else if (tipo == 'K'){
							if (fonte->param2 == 0)
								g=CURTO;
							else
								g=I * fonte->param2*2*M_PI * netlist[i].valor;

							Yn[netlist[i].x][netlist[i].y]+=g;
							Yn[netlist[i].y][netlist[i].x]+=g;
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

					if (fonte->nome[0] =='I') {
						if (strcmp(fonte->tipo,"DC") == 0)
							g=fonte->valor;
						else if (strcmp(fonte->tipo,"SIN") == 0)
							g=fonte->param1*cos(fonte->param6*M_PI/180) + I*fonte->param1*sin(fonte->param6*M_PI/180);
						else if (strcmp(fonte->tipo,"PULSE") == 0)
							g=fonte->valor + I*fonte->valor;

						Yn[fonte->a][nv+1]-=g;
						Yn[fonte->b][nv+1]+=g;
					}
					else if (fonte->nome[0] == 'V') {
						Yn[fonte->a][fonte->x] += 1;
						Yn[fonte->b][fonte->x] -= 1;
						Yn[fonte->x][fonte->a] -= 1;
						Yn[fonte->x][fonte->b] += 1;
						if (strcmp(fonte->tipo,"DC") == 0) {
							Yn[fonte->x][nv+1] -= fonte->valor;
						} else if(strcmp(fonte->tipo,"SIN") == 0) {
							Yn[fonte->x][nv+1] -= fonte->param1*cos(fonte->param6*M_PI/180) + I*fonte->param1*sin(fonte->param6*M_PI/180);
						} else if (strcmp(fonte->tipo,"PULSE") == 0) {
							Yn[fonte->x][nv+1] -= fonte->valor;
						} else {
#ifdef DEBUG
							printf("Tipo da fonte nao identificado\n");
#endif
						}
					}
#ifdef DEBUG
					/* Opcional: Mostra o sistema apos a montagem da estampa */
					//	printf("Sistema apos a estampa de %s\n",netlist[i].nome);
					for (i=1; i<=nv; i++) {
						for (j=1; j<=nv+1; j++)
							if (cabs(Yn[i][j])!=0)
								printf("%+3.1f + j%+3.1f ",creal(Yn[i][j]),cimag(Yn[i][j]));
							else
								printf(" ........... ");
						printf("\n");
					}
#endif
#if defined(_WIN32) && defined(DEBUG)
					getch();
#endif
					/* Resolve o sistema */
					// Se o sistema for singular para essa fonte, vamos ignorar sua contribuição na superposição.
					if (resolversistema() == 0) {
						/* Opcional: Mostra o sistema resolvido */
#ifdef DEBUG
						printf("Sistema resolvido:\n");
#endif
						float fasor;
						double tOff;
						for (i=1; i<=nv; i++) {
							for (j=1; j<=nv+1; j++) {

								if (fonte->param2 == 0)
									fasor = creal(Yn[i][j]);
								else {
									if (strcmp(fonte->tipo,"SIN") == 0){
										fasor = cabs(Yn[i][j])*sin(indiceHarmonicos*fonte->param2*2*M_PI*t + carg(Yn[i][j]));
									}else if (strcmp(fonte->tipo,"PULSE") == 0){
										fasor = cabs(Yn[i][j])*cos(fonte->param2*2*M_PI*t + carg(Yn[i][j]));
									}
								}
								Yt[i][j] += fasor;
#ifdef DEBUG
								if (Yn[i][j]!=0)
									printf("%+3.1f ",fasor);
								else
									printf(" ... ");
#endif
							}
#ifdef DEBUG
							printf("\n");
#endif
						}
#if defined(_WIN32) && defined(DEBUG)
						getch();
#endif
					}

					if (strcmp(fonte->tipo,"PULSE") ==0 && fonte->param2 >0) {

					for (i=0; i<=nv; i++) {
						for (j=0; j<=nv+1; j++)
							Yn[i][j]=0;
					}
					/* Monta estampas */
					for (i=1; i<=ne; i++) {
						tipo=netlist[i].nome[0];
						if (tipo == 'V' && i != indiceFonte) {
							Yn[netlist[i].a][netlist[i].x]+=1;
							Yn[netlist[i].b][netlist[i].x]-=1;
							Yn[netlist[i].x][netlist[i].a]-=1;
							Yn[netlist[i].x][netlist[i].b]+=1;
							Yn[netlist[i].x][nv+1]-=0;
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
							if (fonte->param2 == 0)
								g = 1/ABERTO;
							else
								g=I * fonte->param2*2*M_PI * netlist[i].valor;

							//printf("Capacitor - impedancia=%f + j%f\n",creal(g),cimag(g));
							Yn[netlist[i].a][netlist[i].a]+=g;
							Yn[netlist[i].b][netlist[i].b]+=g;
							Yn[netlist[i].a][netlist[i].b]-=g;
							Yn[netlist[i].b][netlist[i].a]-=g;
						}
						else if(tipo=='L'){
							if (fonte->param2 == 0)
								g=CURTO;
							else
								g=I * fonte->param2*2*M_PI * netlist[i].valor;

							Yn[netlist[i].a][netlist[i].x]+=1;
							Yn[netlist[i].b][netlist[i].x]-=1;
							Yn[netlist[i].x][netlist[i].a]-=1;
							Yn[netlist[i].x][netlist[i].b]+=1;
							Yn[netlist[i].x][netlist[i].x]+=g;
						}
						else if (tipo == 'K'){
							if (fonte->param2 == 0)
								g=CURTO;
							else
								g=I * fonte->param2*2*M_PI * netlist[i].valor;

							Yn[netlist[i].x][netlist[i].y]+=g;
							Yn[netlist[i].y][netlist[i].x]+=g;
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

					if (fonte->nome[0] =='I') {
						g=fonte->param1;
						Yn[fonte->a][nv+1]-=g;
						Yn[fonte->b][nv+1]+=g;
					}
					else if (fonte->nome[0] == 'V') {
						Yn[fonte->a][fonte->x] += 1;
						Yn[fonte->b][fonte->x] -= 1;
						Yn[fonte->x][fonte->a] -= 1;
						Yn[fonte->x][fonte->b] += 1;
						Yn[fonte->x][nv+1] -= fonte->param1;
					}
#ifdef DEBUG
					/* Opcional: Mostra o sistema apos a montagem da estampa */
					//	printf("Sistema apos a estampa de %s\n",netlist[i].nome);
					for (i=1; i<=nv; i++) {
						for (j=1; j<=nv+1; j++)
							if (cabs(Yn[i][j])!=0)
								printf("%+3.1f + j%+3.1f ",creal(Yn[i][j]),cimag(Yn[i][j]));
							else
								printf(" ........... ");
						printf("\n");
					}
#endif
#if defined(_WIN32) && defined(DEBUG)
					getch();
#endif
					/* Resolve o sistema */
					// Se o sistema for singular para essa fonte, vamos ignorar sua contribuição na superposição.
					if (resolversistema() == 0) {
						/* Opcional: Mostra o sistema resolvido */
#ifdef DEBUG
						printf("Sistema resolvido:\n");
#endif
						float fasor;
						double tOff;
						for (i=1; i<=nv; i++) {
							for (j=1; j<=nv+1; j++) {

								fasor = cabs(Yn[i][j])*sin(fonte->param2*2*M_PI*t + carg(Yn[i][j]));

								Yt[i][j] += fasor;
#ifdef DEBUG
								if (Yn[i][j]!=0)
									printf("%+3.1f ",fasor);
								else
									printf(" ... ");
#endif
							}
#ifdef DEBUG
							printf("\n");
#endif
						}
#if defined(_WIN32) && defined(DEBUG)
						getch();
#endif
					}
					}



					free(fonte);
				}
			}
		}

		fprintf(outputFile,"%g",t);

		/* Mostra solucao */
#ifdef DEBUG
		printf("Solucao:\n");
		strcpy(txt,"Tensao");
#endif
		for (i=1; i<=nv; i++) {
			fprintf(outputFile," %g",Yt[i][nv+1]);
#ifdef DEBUG
			if (i==nn+1)
				strcpy(txt,"Corrente");
			printf("%s %s: %g\n",txt,lista[i],Yt[i][nv+1]);
#endif
		}
		fprintf(outputFile,"\n");

#ifdef DEBUG
		printf("Tempo atual: %f\n",t);
		printf("Passo: %f\n",passo);
		printf("Tempo Final: %f\n",tempoFinal);
#endif
		t = t + passo;
#if defined(_WIN32) && defined(DEBUG)
		getch();
#endif
	}while(t<tempoFinal);

	fclose(outputFile);
	printf("Analise concluida. O resultado está salvo no arquivo %s\n",outputFilename);
	return 0;
}

