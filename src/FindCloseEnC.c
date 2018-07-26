/*
 ============================================================================
 Name        : FindCloseEnC.c
 Author      : jesica
 Version     :
 Copyright   : Your copyright notice
 Description : Hello World in C, Ansi-style
 ============================================================================
 */

#include <stdio.h>
#include <stdlib.h>


#include <stdint.h>
//#include <iostream>
#include <math.h>
#include <string.h>

/* only for getTime() */
#include <sys/time.h>
#include <sys/resource.h>

#include <time.h>

//using namespace std;

//defino el tipo ulong
#ifndef ulong  //Este debería llamarse uint pero le pongo ulong porque tengo todo el código de tipo ulong
#define ulong unsigned int
#endif

///////// cantidad de elementos que pediremos en cada asignacion de memoria
#define numberElementsPilaToRequest 8
#define numberNodesToRequest 10
#define numberLeavesToRequest 10
#define numberPositionCloseToRequest 10

/*
 * ###################################### INICIO CODIGO Findclose Dario.######################################### */
#define DIV(a) ((a)>> 3)
#define MOD(a) ((a) & 7)

// a/32 y a%32
#define DIVb(a) ((a)>> 5)
#define MODb(a) ((a) & 31)

// a/s y a%s
#define DIVs(a) ((a)>> 7)//Aquí asumimos que s=4 y b=32 por lo que s*b=128 --> 2^7=128.
#define MODs(a) ((a) & ((s*b)-1))

#define MIN(a,b) (a<b) ? a : b
#define error(msg) {printf("\n error, ");printf(msg); printf("\n");exit(1);}


typedef unsigned char byte;
#ifndef uchar
#define uchar unsigned char
#endif

byte RankTable[255];
char MinExcessTable[255];
char *MinExcessBitmap;  //estructura que mantiene los excesos minimos del bitmap que representa la estructura del árbol
char *MinExcessBitmap_RS;  //estructura que mantiene los excesos minimos del bitmap que representa la estructura del árbol para un total de (RS*b) bit
byte NumOfLeaves[255];

#define mask31 0x0000001F

#define max(x,y) ((x)>(y)?(x):(y))
#define min(x,y) ((x)<(y)?(x):(y))

/*numero de bits del entero de la maquina*/
#define W 32
/* W-1 */
#define Wminusone 31
/*numero de bits del entero de la maquina*/
#define WW 64
/*bits para hacer la mascara para contar mas rapido*/
#define bitsM 8
/*bytes que hacen una palabra */
#define BW 4

#ifndef uchar
#define uchar unsigned char
#endif

#define size_uchar 256

#define true 1

#define false 0

const unsigned char popcount_tab[] =
{
0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,
1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8,
};


ulong *bitmap_ulong, b=32,s=4; //Variable utilizada para mantener el arreglo de parentesis luego de convertirlo a ulong.

/**********************************************
        Procesos que estaban como inline
**********************************************/
ulong popLeaves (register int x, int *bandera) {
	ulong y;
	y =  NumOfLeaves[(x >>  0) & 0xff]  + NumOfLeaves[(x >>  8) & 0xff]  + NumOfLeaves[(x >> 16) & 0xff]  + NumOfLeaves[(x >> 24) & 0xff];

	//bandera es la variable que indica si el nro que se chequeo previamente terminaba en 1, si es así y además el ulong actual empieza con cero, estamos en presencia de una hoja.
	if (*bandera && (((x >>  24) & 0xff) < 128)) y=y+1;

	//Realizamos el & (and logico) con uno porque necesitamos saber si el nro es par o impar y con esta operación realizamos el modulo 2 de un nro.
	if ((((x >>  24) & 0xff) & 1) && (((x >>  16) & 0xff) < 128))
			y=y+1;

	if ((((x >>  16) & 0xff) & 1) && (((x >>  8) & 0xff) < 128))
				y=y+1;

	if ((((x >>  8) & 0xff) & 1) && (((x >>  0) & 0xff) < 128))
				y=y+1;

	//Si el byte menos significativo del ulong termina en 1 debemos ver si el byte mas significativo del ulong siguiente compienza con cero, en tal caso estamos en presencia de una hoja.
	if (((x >>  0) & 0xff) & 1)
		*bandera=1;
	else
		*bandera=0;

	return (y);
	}

ulong popcount (register int x) {
   return ( popcount_tab[(x >>  0) & 0xff]  + popcount_tab[(x >>  8) & 0xff]  +
            popcount_tab[(x >> 16) & 0xff]  + popcount_tab[(x >> 24) & 0xff] );
}




//#define error(msg) {printf("\n error, ");printf(msg); printf("\n");exit(1);}
//------------------------------------------------------------------------------------------
// Crea tablas con cantidad de unos, exceso de ceros y cantidad de hijos de los nro 0 al 255
//------------------------------------------------------------------------------------------
void initRankExcLeavesTables()
{
ulong i, j, aux;
char actualExcess;
int is_one;

      memset(RankTable,0, 255);
      memset(MinExcessTable,8, 255);
      memset(NumOfLeaves,0,255);
      for (i=0; i<256; i++)
      {	    actualExcess=0; aux=i; is_one=0;
            for (j=0; j<8; j++)
            {      if (aux&128)
                   {   RankTable[i]++; actualExcess++;is_one=1;}
                   else
                   {   actualExcess--;
                   	   if(is_one)
                   	   {  NumOfLeaves[i]++; is_one=0;}
                   }

                   if (actualExcess < MinExcessTable[i])
                        MinExcessTable[i]=actualExcess;
                   aux =aux<<1;
            }
      }

}

// FIN --- Crea tablas con cantidad de unos, exceso de ceros y cantidad de hijos de los nro 0 al 255
//------------------------------------------------------------------------------------------


// Convierte un arreglo de uchar a uno de ulong
//bitmap_char arreglo de uchar a convertir tener en cuenta que nos devuelve un arreglo de ulong sin modificar el
//arreglo de uchar
//bitmap_long arreglo de ulong en el que será devuelto el arreglo convertido
//cant_bits_bitmap cantidad de bit que tiene el arreglo de uchar
void uchartoulong(byte *bitmap_char, ulong **bitmap_long, ulong cant_bits_bitmap){
	int i, aux, aux2;
	ulong tam_bitmap_byte, tam_bitmap_ulong;
	byte *bitmap_char_aux;

	if MODb(cant_bits_bitmap){
		tam_bitmap_byte= DIV(cant_bits_bitmap)+4;
		tam_bitmap_ulong= DIVb(cant_bits_bitmap)+1;
	}
	else{
		tam_bitmap_byte= DIV(cant_bits_bitmap);
		tam_bitmap_ulong= DIVb(cant_bits_bitmap)+1;
	}

	bitmap_char_aux=(byte *)malloc(sizeof(byte)*tam_bitmap_byte);
	*bitmap_long=(ulong *)malloc(sizeof(ulong)*tam_bitmap_ulong);
	//*bitmap_long=(ulong *)realloc(*bitmap_long,tam_bitmap_ulong);

	memset(bitmap_char_aux,0, tam_bitmap_byte);
	memset(*bitmap_long,0, tam_bitmap_ulong);

	i=4;
	aux=0;
	aux2=i-1;
	while (i<= tam_bitmap_byte)
	{
		while (aux<i){
			bitmap_char_aux[aux2]=bitmap_char[aux];
			aux2-=1;
			aux+=1;
		}
		i=i+4;
		aux2=i-1;
	}

	*bitmap_long=(ulong *)bitmap_char_aux;
}



//------------------------------------------------------------------------------------------
// Crea tablas con exceso de ceros tomando de a 32 bit (4 Bytes) del Bipmap creado
// bitmap: es la estructura que mantiene los bit que conforman la estructura del árbol
// MinExcessBitmap: es un tabla global que mantiene los excesos minimos del bitmap
// last: Cantidad de bytes que tiene el bitmap
// b: variable global que nos da el tamaño del registro.
//------------------------------------------------------------------------------------------
void initExcBitmapTables(ulong *bitmap,ulong last)
{
	ulong i, j, aux, ulong_size_bitmap, cant_bit_sobrantes, Rs_size_bitmap, is=0, cur_is=0;
	char actualExcess;
	char actualExcess_Rs; //Mantiene el exceso minimo para la estructura Rs

	  ulong_size_bitmap=DIVb(last);  //Ver el tema si modificamos b #define DIVS(a) ((a)>> 5)
	  Rs_size_bitmap=DIVs(last);

	  MinExcessBitmap=(char *)realloc(MinExcessBitmap,ulong_size_bitmap+1);
      memset(MinExcessBitmap,8, ulong_size_bitmap+1);

      MinExcessBitmap_RS=(char *)realloc(MinExcessBitmap_RS,Rs_size_bitmap+1);
      memset(MinExcessBitmap_RS,8, Rs_size_bitmap+1);

      actualExcess_Rs=0;
	  for (i=0; i<ulong_size_bitmap; i++)
	  {	    actualExcess=0; aux=bitmap[i];
			if (is==s) //La estructura MinExcessBitmap_RS toma de a "s" ulong
			{
				cur_is+=1;
				actualExcess_Rs=0;
				is=0;
			}

			for (j=0; j<32; j++)
			{      if (aux&(1<<b-1))
					{ //2147483648 en binario  1000 0000 0000 0000 0000 0000 0000 0000  (2^(b-1))
					  actualExcess++;
					  actualExcess_Rs++;
					}
				   else
				   {
					 actualExcess--;
					 actualExcess_Rs--;
				   }

				   if (actualExcess < MinExcessBitmap[i])
						MinExcessBitmap[i]=actualExcess;
				   if (actualExcess_Rs < MinExcessBitmap_RS[cur_is])
					    MinExcessBitmap_RS[cur_is]=actualExcess_Rs;
				   aux=aux<<1;
			}
			is+=1;
	  }

	  if(MODs(last)<=32){cur_is+=1;actualExcess_Rs=0;}

      if (cant_bit_sobrantes=MODb(last)){ //En esta sección sacamos el exceso del los últimos bit, es decir puede suceder que nuestro bitmap tenga T modulos de 32bit y el último sólo resten de 0 a 31 bit por lo tanto debemos realizar un trabajo diferenciados sobre ellos
    	  // MODS(a) ((a) & 31)
    	  actualExcess=0; aux=bitmap[i];
    	  for (j=0; j<cant_bit_sobrantes; j++)//cant_bit_sobrantes es la cantidad de bits que no completan un ulong de 32 bits
    	  {   if (aux&(2^(cant_bit_sobrantes-1)))
    	  	  {
    		  	  actualExcess++;
    		  	  actualExcess_Rs++;
    	  	  }
    	  	  else
    	  	  {
    	  		  actualExcess--;
    	  		  actualExcess_Rs--;
    	  	  }
    	  	  if (actualExcess < MinExcessBitmap[i])
    	  		  MinExcessBitmap[i]=actualExcess;
    	  	  if (actualExcess < MinExcessBitmap_RS[cur_is])
    	  		  MinExcessBitmap_RS[cur_is]=actualExcess_Rs;
    	  	  aux =aux<<1;
    	  }
      }

}


int isleaf(byte *tree,ulong pos)
{
	pos++;
	if(tree[DIV(pos)] & (128>> MOD(pos++)))
		return 0; //No es hoja
	else
		return 1; //es hoja
}


ulong FindCloseOrig(ulong *bitmap_ulong, ulong pos, ulong last, ulong *nroNodo, ulong *nroHoja)
{
		ulong *A;

		A=bitmap_ulong;
		int E, is_one=0,bandera, break_byte=1, break_ulong=1, cont_s;
 	    ulong *aux_ulong, *aux_ulong2,pos_aux, exce_maximo=0;
 	    byte *aux_byte, *aux_byte2;
 	    int pos_bits, of_bits=0;
 	 	aux_ulong=(ulong *) malloc(sizeof(ulong)*1);
 	 	aux_ulong2=(ulong *) malloc(sizeof(ulong)*1);

 	 	*aux_ulong = A[DIVb(pos)];
 	 	aux_byte=(byte *)aux_ulong;

 	 	pos_bits=MODb(pos);

 	 	E=-1; pos++; pos_bits++;

		 if ((MODs(pos))) { //Si esta en posición modulo s*b = 0  directamente procesamos de a s*b bit

			if ((MODb(pos))) { //Si esta en posición modulo 32 = 0  directamente procesamos de a ulong

				 //********************   Procesa de a bits *******************//
				// procesamos los primeros bits hasta llegar al inicio de un byte

				 if (MOD(pos_bits))
				 {of_bits=1;
					 while ( MOD(pos_bits) && E!=0)
					 {     if (aux_byte[3-DIV(pos_bits)] & (128>> MOD(pos_bits++)) )
						   { E--; is_one=1; (*nroNodo)++;}
						   else
						   { E++;
							 if(is_one){(*nroHoja)++;is_one=0;}
						   }
						 pos++;
					 }
				 }
				 else{ //else MOD --Verificamos si el cero correspondiente al uno se encuentra el el inicio del
					 //byte. Estariamos en presencia de un hoja que tiene su 1 en un byte y su cero el inicio del
					 //proximo byte.
					 if (!(aux_byte[3-DIV(pos_bits)] & (128>> MOD(pos_bits)) ))
					 { E++; pos++; pos_bits++;}
				 }
				/*if ((!(MOD(pos))) && pos < last)
					if ( ((A[DIV(pos)-1]) & (128>> 7)) && (A[DIV(pos)] < 128) ) (*nroHoja)++;//Realizamos esta consulta para saber si el nro anterior termina en 1 y el siguiente empieza en 0, si este es el caso estamos en presencia de una hoja.
				*/
			}
			else{//else MODb -- Sólo ingresa cuando búscamos el cero para el uno que esta al final de un ulong y
				//verificamos si el siguiente ulong comienza con 0, podemos ver que es una hoja cuyo uno esta al
				//final de un ulong y su cero esta al inicio del siguiente ulong.
				*aux_ulong = A[DIVb(pos)];
				aux_byte=(byte *)aux_ulong;
				pos_bits=MODb(pos);
				if (!(aux_byte[3-DIV(pos_bits)] & (128>> MOD(pos_bits)) ))
				{ E++; pos++;pos_bits++;}
			}
		 }
		 else //else MODs  --
		 {  if (!(A[DIVb(pos)]&(1<<b-1)))
				{ E++; pos++;pos_bits++;}
		 }


        //********************   Procesa de a bytes *******************//

	 if ((MODs(pos))){  //Si esta en posición modulo s*b = 0  directamente procesamos de a s*b bit

        if ((MODb(pos))) {
			// se procesa de a bytes
        	// bandera=0;  Descomenar en caso de realizar el proceso de hojas llamando a pop_leaves
			while (pos+8 < last && E!=0 && MODb(pos))  //RECORDAR QUE PUSIMOS <= last DEBEMOS PROBAR SI FUNCIONA
			{
				  if (of_bits){//Si pos_bit dividido 8 da cero (0). Estamos en el situación donde pos_bit queda sobre el bit cero de nuestra estructura y por lo tanto no se ha hecho un procesamiento de a bits.
					  if ( ((aux_byte[3-DIV(pos_bits)+1]) & (128>> 7)) && (aux_byte[3-DIV(pos_bits)] < 128) ) (*nroHoja)++;//Realizamos esta consulta para saber si el nro anterior termina en 1 y el siguiente empieza en 0, si este es el caso estamos en presencia de una hoja.
				  }
				  else
					  of_bits=1;
				  if ( MinExcessTable[ aux_byte[3-DIV(pos_bits)] ] <= E){
					  break_byte=0;
					  break;double time, tot_time = 0;
				  }
				  else  { E -= 2 * RankTable[ aux_byte[3-DIV(pos_bits)] ] - 8 ; //exceso total
				  //      E -= 2 * popcount8(aux_byte[3-DIV(pos_bits)]) - 8 ; //exceso total
						  (*nroNodo)+= RankTable [ aux_byte[3-DIV(pos_bits)]];
						//(*nroNodo)+=popcount8(aux_byte[3-DIV(pos_bits)]);
						  (*nroHoja)+= NumOfLeaves[ aux_byte[3-DIV(pos_bits)]];
						//(*nroHoja)+=popLeaves8(aux_byte[3-DIV(pos_bits)], &bandera);
						}
				  pos+=8;
				  pos_bits+=8;
			  //if ( ((A[DIV(pos)-1]) & (128>> 7)) && (A[DIV(pos)] < 128) ) (*nroHoja)++;
			}
        }
	 }


		if (break_byte){
			if((aux_byte[0] & 128>> 7) && of_bits)
				bandera=1;
			else
				bandera=0;

			//********************   Procesa de a ulong *******************//
			while (pos+b < last && E!=0 && MODs(pos))
				// se procesa de a ulong
			{     if ( MinExcessBitmap[ DIVb(pos) ] <= E){
						break_ulong=0;
						break;
					}
				  else  { E -= 2 * popcount( A[DIVb(pos)] ) - b ; //exceso total b=32 en este caso
						  (*nroNodo)+= popcount ( A[DIVb(pos)]);
						  (*nroHoja)+= popLeaves( A[DIVb(pos)], &bandera);
						}
				  pos+=b;

			}


			if (break_ulong){
			//********************   Procesa de a (s*b) bit *******************//
				while (pos+(b*s) < last && E!=0)
				{
					//if(pos>=14011554 && pos<=14011810)
						//cont_s=0;
					  cont_s=0;
					  exce_maximo=0;
					  if ( MinExcessBitmap_RS[ DIVs(pos) ] <= E)
							break;
					  else
					  {
						  pos_aux=DIVb(pos);
						  while(cont_s<s){
							  exce_maximo+= popcount( A[pos_aux] );
							  (*nroNodo)+= popcount ( A[pos_aux]);
							  (*nroHoja)+= popLeaves( A[pos_aux], &bandera);
							  pos_aux+=1;
							  cont_s+=1;
						  }
						  E -= 2 * exce_maximo - b*s ; //exceso total s*b
					   }
					  pos+=b*s;
				}
			}


			//********************   Procesa de a ulong *******************//
			while (pos+b < last && E!=0)
				// se procesa de a ulong
			{     if ( MinExcessBitmap[ DIVb(pos) ] <= E)
						break;

				  else  { E -= 2 * popcount( A[DIVb(pos)] ) - b ; //exceso total b=32 en este caso
						  (*nroNodo)+= popcount ( A[DIVb(pos)]);
						  (*nroHoja)+= popLeaves( A[DIVb(pos)], &bandera);
						}
				  pos+=b;
			}


			if (E!=0)
				if (!(A[DIVb(pos)]&(1<<b-1)) && bandera) (*nroHoja)++;
				/*
				*aux_ulong = A[DIVb(pos)];
				*aux_ulong2 = A[DIVb(pos)-1];
				aux_byte=(byte *)aux_ulong;
				aux_byte2=(byte *)aux_ulong2;
				pos_bits=MODb(pos);
				if ( ((aux_byte2[0]) & (128>> 7)) && (aux_byte[3-DIV(pos_bits)] < 128) ) (*nroHoja)++; //Realizamos esta consulta para saber si el nro anterior termina en 1 y el siguiente empieza en 0, si este es el caso estamos en presencia de una hoja.
				*/
		}


		//********************   Procesa de a bytes *******************//

		//Esta pensado para trabajar con b=32 por lo tanto siempre que frene la iteración anterior es porque llegamos al final o no existen b bit pas procesar. En este último caso siempre queda sobre el comienzo de un byte
		// se procesa de a bytes
        *aux_ulong2=0; //Es utilizado para
        *aux_ulong = A[DIVb(pos)];
        aux_byte=(byte *)aux_ulong;
        pos_bits=MODb(pos);
		while (pos+8 < last && E!=0)
		{
			if (*aux_ulong2){ //Aquí se debe realizar esta pregunta luego de haber avanzado al menos una ves en el byte en cuestión
				if ( ((aux_byte[3-DIV(pos_bits)+1]) & (128>> 7)) && (aux_byte[3-DIV(pos_bits)] < 128) ) (*nroHoja)++; //Realizamos esta consulta para saber si el nro anterior termina en 1 y el siguiente empieza en 0, si este es el caso estamos en presencia de una hoja.

			}
			else
				*aux_ulong2=1;

			if ( MinExcessTable[ aux_byte[3-DIV(pos_bits)] ] <= E)
				  break;
			  else  { E -= 2 * RankTable[ aux_byte[3-DIV(pos_bits)] ] - 8 ; //exceso total
			        //E -= 2 * popcount8(aux_byte[3-DIV(pos_bits)]) - 8 ; //exceso total
					  (*nroNodo)+= RankTable [ aux_byte[3-DIV(pos_bits)]];
					//(*nroNodo)+=popcount8(aux_byte[3-DIV(pos_bits)]);
					  (*nroHoja)+= NumOfLeaves[ aux_byte[3-DIV(pos_bits)]];
					//(*nroHoja)+=popLeaves8(aux_byte[3-DIV(pos_bits)], &bandera);
					}
			  pos+=8;
			  pos_bits+=8;
		  //if ( ((A[DIV(pos)-1]) & (128>> 7)) && (A[DIV(pos)] < 128) ) (*nroHoja)++;
		}


		//********************   Procesa de a bits *******************//
		if (pos+8 >= last && E!=0){
				if ((pos<last) && ((aux_byte[3-DIV(pos_bits)+1]) & (128>> 7)) && (aux_byte[3-DIV(pos_bits)] < 128) ) (*nroHoja)++;}
		is_one=0;
        while (E!=0 && pos <last)
        {
        		if (aux_byte[3-DIV(pos_bits)] & (128>> MOD(pos_bits++)) )
               { E--; is_one=1; (*nroNodo)++;}
               else
               { E++;
               	 if(is_one){(*nroHoja)++;is_one=0;}
               }
        	pos++;
        }

        free(aux_ulong);
        free(aux_ulong2);
        //free(aux_byte);
        //free(aux_byte2);
        if (E!=0)
              error ("en FindClose, no lo encontro");
        return (pos-1);
}



/* #######################################   FIN CODIGO DARIO ###################################### */


/* ################################################  CODIGO MIO ################################################## */
//-----------------------------------------------------------------
///------------------------------> PILA
typedef struct tipoPila {
	ulong positionArray;
	ulong nodes;
	ulong leaves;
	ulong positionBit;
	ulong positionInitial;
} tipoPila;


tipoPila *pila;
long topePila;
ulong endIndexPila=0; //Marca el limite superior de la estructuras Pila de acuerdo a la cantidad de elementos pedidos con ralloc

///<------------------------------ fin PILA
//-----------------------------------------------------------------


///------------------------------> Arreglos con los resultados del findClose ------------------------------------------------------------
// arreglos por separados para guardar el resultado de cada nivel del findClose
//1) Arreglo que guarda la cantidad de nodos (OJO: recordar que no se llena consecutivamente puede llenarse primero la posicion 3 luego la 1, luego la 4 y luego la 2)
ulong *nodes;
ulong totalCountNodes = 0; 		//cantidad total de nodos (usados + sin uso), cantidad de elementos asignados con el ralloc que no necesariamente significa que esten todos usados.
ulong totalCountNodesUsed = 0; 	//cantidad total de NODOS USADOS.

//2) Arreglo que guarda la cantidad de hojas
ulong *leaves;
ulong totalCountLeaves = 0; 	//cantidad total de hojas (usadas + sin uso), cantidad de elementos asignados con el ralloc que no necesariamente significa que esten todos usados.
ulong totalCountLeavesUsed = 0; //cantidad total de HOJAS USADAS.


//3) Arreglo que guarda las posiciones de cierre
ulong *positionClose;
ulong totalCountPositionClose = 0; 		//cantidad total de posiciones de cierre (usadas + sin uso), cantidad de elementos asignados con el ralloc que no necesariamente significa que esten todos usados.
ulong totalCountPositionCloseUsed = 0; 	//cantidad total de POSICIONES DE CIERRE USADAS
///<------------------------------------------------------------------------------------------------------------------------

ulong positionArrayClose = 0; //equiv a Posnivel
ulong lastPosArrayUsed = 0;

//map<ulong,ulong> mapa;

void verif(void *p)
{
	if (p == NULL)
		error ("sin memoria\n");
}

//==============================================================================================================
//================================> INICIO METODOS para las estructuras con el RESULTADO DEL FINDCLOSE

//-----------------------------------------------------------------
/** Asignar espacio si hace falta para estructura de tipo ulong (Nodes, Leaves, PositionClose)
//-----------------------------------------------------------------
 * arrayULong: apuntador a estructura para asignar memoria
 * totalCount: cantidad de elementos totales en la estructura
 * usedCount: cantidad de lugares ya usados para la estructura ptr //TODO creo que no se usa, si es asi sacar
 * countToRequest: cantidad de bloques de asignación de memoria a solicitar
 * posToInsert: posicion en la que se quiere insertar
 */
void addSpaceStructUlong(ulong **arrayULong, ulong *totalCount, ulong *usedCount, int countToRequest, ulong posToInsert)
{
	int i= *totalCount;
	while(posToInsert >= *totalCount)
	{
		*totalCount=*totalCount+countToRequest;
		*arrayULong=(ulong *)realloc(*arrayULong,((*totalCount)*sizeof(ulong)));
		verif(*arrayULong);
	}

	//lleno con 0 los lugares agregados a partir de la 'ultima posicion disponible antes de asignar mas lugares' hasta la 'ultima posicion luego de agregar lugares'
	while (i < *totalCount)//TODO ver si es < o <=
	{
		(*arrayULong)[i]=0;
		i++;
	}
}
//<================================ fin METODOS para las estructuras con el RESULTADO DEL FINDCLOSE


//==============================================================================================================
//================================> INICIO METODOS PILA

//-----------------------------------------------------------------
//verifica memoria pedida
//-----------------------------------------------------------------

void verifySpace(void *p)
{
	if (p == NULL)
		error ("sin memoria\n");
}


//-----------------------------------------------------------------
//Asignar espacio si hace falta para estructura Pila
//-----------------------------------------------------------------
//ptr apuntador a estructura para asignar memoria
//n cantidad de elementos actuales en la estructura
//end_index cantidad de lugares ya asignados para la estructura ptr
//blk_pila cantidad de bloques de asignación de memoria a solicitar
void addSpacePila(tipoPila ***ptr, ulong n, ulong *end_index, int blk_pila)
{
	if( *end_index == n )
	{
		int i=0;
		*end_index=*end_index+blk_pila;//
		**ptr=(tipoPila *)realloc(**ptr,((*end_index)*sizeof(tipoPila)));
		verifySpace(**ptr);
		while (i<blk_pila) //Inicializamos los campos de la pila recién asignados
		{
			(**ptr)[n].positionArray=0;
			(**ptr)[n].nodes=0;
			(**ptr)[n].leaves=0;
			(**ptr)[n].positionBit=0;
			(**ptr)[n].positionInitial=0;
			i++;
			n++;
		}
	}
}

void push(tipoPila **l, tipoPila v){
	int bloques = numberElementsPilaToRequest;
	addSpacePila(&l, topePila+1, &endIndexPila, bloques);
	topePila++;
	(*l)[topePila].positionArray= v.positionArray;
	(*l)[topePila].nodes = v.nodes;
	(*l)[topePila].leaves = v.leaves;
	(*l)[topePila].positionBit = v.positionBit;
	(*l)[topePila].positionInitial = v.positionInitial;

};

int pop() {
	topePila--;
	return 1;
};

int empty () {
	if (topePila == -1)
		return 1;
	else
		return 0;
};

void copyPreviousElement(tipoPila **l, ulong lastWasZero)
{
	//Solo en la ultima posicion de la pila se incrementa con un "1" mas.
	if(topePila == 1 || lastWasZero==1)
	{
		(*l)[topePila-1].nodes = (*l)[topePila-1].nodes + (*l)[topePila].nodes + 1;
	}
	else
	{
		(*l)[topePila-1].nodes = (*l)[topePila-1].nodes + (*l)[topePila].nodes;
	}
	(*l)[topePila-1].leaves = (*l)[topePila-1].leaves + (*l)[topePila].leaves;
	(*l)[topePila-1].positionBit = (*l)[topePila].positionBit;


	if(topePila >1 && ( ((*l)[topePila-1].positionArray)==0 ) )
	{
		if(lastPosArrayUsed > positionArrayClose)
		{
			lastPosArrayUsed = lastPosArrayUsed + 1;
		}
		else
		{
			lastPosArrayUsed = positionArrayClose + 1;
		}
		(*l)[topePila-1].positionArray = lastPosArrayUsed;
	}
}

void initNode(tipoPila *nodoPila)
{
	nodoPila->nodes=0;
	nodoPila->leaves=0;
	nodoPila->positionBit=0;
	nodoPila->positionInitial=0;
	if(topePila >= 0)
	{
		if(pila[topePila].positionArray > positionArrayClose)
		{
			nodoPila->positionArray= pila[topePila].positionArray +1;
		}
		else
		{
			nodoPila->positionArray= positionArrayClose +1;
		}
	}
	else
	{
		nodoPila->positionArray=0;
	}
}

//<================================ fin METODOS PILA


/**
 * Metodo que calcula las posiciones de cierre, cantidad de nodos y cantidad de hojas.
 *
 * text: arreglo de caracteres que contiene el texto en bytes.
 * size: tamaño del arreglo de caracteres text.
 * bitsCount: cantidad de bits porque puede que el texto tenga una cantidad de bits que no necesariamente sea multiplo de 8 (cant de bits en un byte)
 * 		por ejemplo el texto = 11001001110 tiene 11 bits que seran recibidos como 2 bytes (en text[]) un byte = 11001001, otro byte = 11000000 este ultimo se completa con 0's
 * level: indica el nivel hasta donde queremos calcular.
 */
void buildFindClose(ulong text[], ulong size, ulong bitsCount, ulong level, char *fileOutputModifiedBuilding)
{
	ulong arrayPos = 0;
	ulong bitToByte = 0;
	ulong lastWasZero=0;
	topePila=-1;

	tipoPila nodoPila;

// >>>>>>>>>>>>>>> vbles para medir tiempo de ejecucion de findclose y count.
	clock_t initTimeBuilding, finTimeBuilding;
	double totalTimeBuilding = 0;
// <<<<<<<<<<<<<<< FIN Vbles para medir tiempo de ejecucion de findclose y count.

	//Abro file para escribir el resultado de construir las estructuras necesarias para el findclose mejorado
	FILE *fileBuildResult;
	if((fileBuildResult=fopen(fileOutputModifiedBuilding,"w+"))==NULL)
	{
		printf("--------------------\n");
		printf("**Error: archivo %s no encontrado \n", fileOutputModifiedBuilding);
	}else
	{
		printf("Archivo de resultado del search abierto\n");
	}

	initTimeBuilding = clock();

	//itero cada bit segun la cantidad de bits que me pasaron por parametro
	for(ulong eachBit=0; eachBit < bitsCount; eachBit++)
	{
		arrayPos = DIVb(eachBit) ;
		bitToByte = MODb(eachBit);

//		cout << "eachBit:   " << eachBit << endl;
//		cout << "arrayPos:  " << arrayPos << endl;
//		cout << "bitToByte: " << bitToByte << endl;
		//cout << "text[arrayPos]: " << text[arrayPos];

		//evaluo si en esa posicion hay un '1' o un '0'
		// 128 >> bitToByte = 128>>0 o 128>>1 o 128>>2 o 128>>3 o .... 128>>7. Osea va corriendo el 1 de 10000000 (128)
		// 2147483648(decimal) = 10000000000000000000000000000000 (binario) y vamos corriendo el 1
		if(text[arrayPos] & (2147483648 >> bitToByte)) // este "&" devuelve un 'true' si en esa posicion hay un '1' sino devuelve false
		{
			//cout << "es un UNO !!!! "<< endl<< endl;
			initNode(&nodoPila); //inicializo nodos y hojas

			nodoPila.positionBit = eachBit; //copio la posicion del bit dentro de todo el array
			nodoPila.positionInitial = eachBit; //seteo donde comienza el nodo

			push(&pila, nodoPila);//subo en la pila

			lastWasZero = 0;
		}
		else
		{
			if(lastWasZero==1)// si anterior fue un cero
			{
				if(topePila<=level)
				{
					//cout << "es un CERO !!!! y el ultimo fue un CERO"<< endl << endl;
					//1- guardo la posicion del bit que estoy mirando
					pila[topePila].positionBit = eachBit;

					//2- guardo en los arreglos de resultados de findClose cada valor
					//a) guardo en arreglo de nodos
					addSpaceStructUlong(&nodes, &totalCountNodes, &totalCountNodesUsed, numberNodesToRequest, nodoPila.positionArray);
					totalCountNodesUsed ++;
					nodes[pila[topePila].positionArray] = pila[topePila].nodes;

					//b) guardo en arreglo de hojas
					addSpaceStructUlong(&leaves, &totalCountLeaves, &totalCountLeavesUsed, numberLeavesToRequest, nodoPila.positionArray);
					totalCountLeavesUsed ++;
					leaves[pila[topePila].positionArray] = pila[topePila].leaves;

					//c) guardo la posicion del bit
					addSpaceStructUlong(&positionClose, &totalCountPositionClose, &totalCountPositionCloseUsed, numberPositionCloseToRequest, nodoPila.positionArray);
					totalCountPositionCloseUsed ++;
					positionClose[pila[topePila].positionArray] = pila[topePila].positionBit;

					//3-Guardo en el mapa
//					mapa[pila[topePila].positionInitial] = pila[topePila].positionArray;
					//cout << "inicia en = " << pila[topePila].positionInitial << " y el resultado esta en = " << pila[topePila].positionArray << endl;

					//4- actualizo la ultima posicion que hemos completado en los arreglos resultantes del findClose
					if(positionArrayClose < pila[topePila].positionArray)
						positionArrayClose = pila[topePila].positionArray;
				}

				if(topePila > 0)
				{
					copyPreviousElement(&pila, lastWasZero); //5- Bajo la informacion a la posicion anterior en la pila
					pop();//6- Pop pila
				}
			}
			else
			{// si anterior fue un uno
				//cout << "es un CERO !!!! y el ultimo fue un UNO"<< endl<< endl;

				//incremento nodos y hojas
				nodoPila.nodes = nodoPila.nodes + 1;
				nodoPila.leaves = nodoPila.leaves + 1;

				//incremento posbit
				nodoPila.positionBit = eachBit;

				//agregamos la info a la ultima posicion de la pila
				pila[topePila].nodes = nodoPila.nodes;
				pila[topePila].leaves = nodoPila.leaves;
				pila[topePila].positionBit = nodoPila.positionBit;

				if(topePila > 0)
				{
					copyPreviousElement(&pila, lastWasZero); //Anexo la informacion a la posicion anterior en la pila
					pop(); //Pop pila
				}
			}
			lastWasZero = 1;
		}
	}

	finTimeBuilding = clock();
	totalTimeBuilding += (double)(finTimeBuilding - initTimeBuilding);
	printf("Tiempo total de construccion en milisegundos: %f \n", totalTimeBuilding);

	//TODO obtener el tamaño de todos los arreglos resultantes (nodos,hojas y posiciones de cierre) y sumarizarlos para guardar en el file
	ulong totalSize = totalCountPositionCloseUsed*sizeof(ulong)*3;
	fprintf(fileBuildResult, "%d\t%.4f\t%d\n", level, totalTimeBuilding,totalSize);

/*
	cout << endl << "NODES" << endl;
	for(int i =0; i< totalCountNodesUsed ; i++)
	{
		cout << "nodes[" << i << "] = " << nodes[i] << endl;
	}
	cout << endl << "LEAVES" << endl;
	for(int i =0; i< totalCountLeavesUsed ; i++)
	{
		cout << "leaves[" << i << "] = " << leaves[i] << endl;
	}
	cout << endl << "POSITIONES CLOSE" << endl;
	for(int i =0; i< totalCountPositionCloseUsed ; i++)
	{
		cout << "positionClose[" << i << "] = " << positionClose[i] << endl;
	}
	*/
}

/**
 * Me dice si en esa posicion del texto hay un 1 o un 0.
 */
int es_un_uno(ulong text[], ulong pos)
{
	ulong arrayPos = DIVb(pos) ; //(pos >> 3);
	ulong bitToByte = MODb(pos);	//(pos & 7); //va de 0 a 7

	if(text[arrayPos] & (2147483648>> bitToByte))
		return 1;
	else
		return 0;
}

/**
 * Me dice si esa posicion es o no una hoja.
 */
int es_hoja(ulong text[], ulong pos)
{
	pos++;
	if(es_un_uno(text, pos))
		return 0; //No es hoja
	else
		return 1; //es hoja
}

/**
 * Me da el 'nivel actual' para la posicion del 'bit actual' dado por parametro.
 *
 * text		: contiene el texto a evaluar
 * eachBit	: indica la posicion dentro del texto
 * statusNode: nos indica si un nodo esta cerrado o abierto ('a'=abierto, 'c'=cerrado)
 *
 * Hace lo siguiente:
 	 - si en esa posicion hay un 1 y esta abierto ('a'=1) -> incremento nivel (no modifica la condicion)
  	 - si en esa posicion hay un 1 y esta cerrado ('c'=0) -> lo abro ('a')
 	 - si en esa posicion hay un 0 y esta abierto ('a'=1) -> lo cierra ('c')
  	 - si en esa posicion hay un 0 y esta cerrado ('c'=0) -> decrementa nivel
 */
ulong getCurrentLevel(ulong currentPosition, ulong *statusNode, ulong currentLevel, ulong esUnUno)
{
	if(currentPosition==0)
	{
		*statusNode = 1;
		return 0;
	}

	//evaluo si en esa posicion hay un '1' o un '0'
	if(esUnUno)
	{
		if(*statusNode == 1)
			currentLevel++;
		else
			*statusNode = 1;
	}
	else
	{
		if(*statusNode == 1)
			*statusNode = 0;
		else
			currentLevel--;
	}
	//cout << "la posicion " << currentPosition << " esta en el nivel " << currentLevel << endl;
	return currentLevel;
}

ulong myFindClose(ulong currentPosition, ulong *cantNodos, ulong *cantHojas, ulong posMyArrays)
{
	ulong eachPositionClose;

	//usar estructura mia para saber donde cierra X nodo
	//TODO no devolver un mapa sino usar la ultima posicion usada +1, Sacar mapa usando la ultima posicion usada, devuelvo la siguiente
	//positionArrays = mapa[currentPosition];
	eachPositionClose = positionClose[posMyArrays];
	*cantNodos = nodes[posMyArrays];
	*cantHojas = leaves[posMyArrays];

	return eachPositionClose;
}

/* retorna "a - b" en segundos */
double timeval_diff(struct timeval *a, struct timeval *b)
{
  return
    (double)(a->tv_sec + (double)a->tv_usec/1000000) -
    (double)(b->tv_sec + (double)b->tv_usec/1000000);
}

// en milisegundos
double getTime_count (void)
{

    double cpu_time, sistime;
    struct rusage usage_count;

    getrusage (RUSAGE_SELF, &usage_count);

    cpu_time = (double) usage_count.ru_utime.tv_sec +
        (double) usage_count.ru_utime.tv_usec / 1000000.0;

    sistime = (double) usage_count.ru_stime.tv_sec +
        (double) usage_count.ru_stime.tv_usec / 1000000.0;

    return (cpu_time + sistime);

}

/**
 *
 */
void findCloseUnified(ulong *textUlong, ulong bitsCount, ulong currentLevel, ulong givenLevel, ulong eachBit, ulong *posMyArrays, FILE** fileResult, double *totalTimeAllFC)
{
	ulong eachPositionClose;
	ulong cantNodos=0, cantHojas=0;
	ulong eshoja = es_hoja(textUlong, eachBit);

	//struct timeval t_ini, t_fin;
	double t_ini, t_fin;

	if(eshoja)
	{
		eachPositionClose = (eachBit+1);
		fprintf(*fileResult, "%s%d\t%s%d\t%s%d%s\n", "Nivel:",currentLevel, "Posicion:", eachBit, "Cierra en= ", eachPositionClose, " y es una hoja");
		return;
	}

	if(currentLevel > givenLevel)		//uso el findClose de Dario
	{
			t_ini = getTime_count();
		eachPositionClose = FindCloseOrig(textUlong, eachBit, bitsCount, &cantNodos, &cantHojas);
			t_fin = getTime_count();
			*totalTimeAllFC = t_fin-t_ini;
			//printf("t_ini: %f\n",t_ini);
			//printf("t_fin: %f\n",t_fin);

		fprintf(*fileResult, "%s%d\t%s%d\t%s%d\t%s%d\t%s%d\n", "Nivel:",currentLevel, "Posicion:",eachBit, "Cierra en= ",eachPositionClose, "Nodos= ", cantNodos, "Hojas= ", cantHojas);

	}
	else
	{
			t_ini = getTime_count();
		eachPositionClose = myFindClose(eachBit, &cantNodos, &cantHojas, *posMyArrays);
			t_fin = getTime_count();
			*totalTimeAllFC = t_fin-t_ini;

		*posMyArrays +=1;
		fprintf(*fileResult, "%s%d\t%s%d\t%s%d\t%s%d\t%s%d\n", "Nivel:",currentLevel, "Posicion:",eachBit, "Cierra en= ",eachPositionClose, "Nodos= ", cantNodos, "Hojas= ", cantHojas);
	}
}


void getStatics(ulong *textUlong, ulong size, ulong bitsCount, ulong givenLevel, char *fileNameSearchResult)
{
	//provisorios para saber el maximo nivel del arbol
	ulong maxLevel=0;

	ulong currentLevel = 0, posMyArrays=0;
	ulong statusNode = 0; //0=cerrado, 1=abierto

	// >>>>>>>>>>>>>>> vbles para medir tiempo de ejecucion de findclose modificado y original.
		double totalTimeAllFC = 0;
	// <<<<<<<<<<<<<<< FIN Vbles para medir tiempo de ejecucion de findclose y count.

	// Abre el file con el resultado para graficas
	FILE *fileSearchResult;
	if((fileSearchResult=fopen(fileNameSearchResult,"w+"))==NULL)
	{
		printf("--------------------\n");
		printf("**Error: archivo %s no encontrado \n", fileNameSearchResult);
	}else
	{
		printf("Archivo de resultado del search abierto \n");
	}

	// Abre file para escribir los resultados en texto. TODO eliminar
	FILE *fileResult;
	if((fileResult=fopen("/home/jesica/Documents/tesis/ejecucion/results/solo_para_mi/cierres_modified.txt","w+"))==NULL)
	{
		printf("--------------------\n");
		printf("**Error: archivo cierres_modified no encontrado\n");
	}
	else{
		printf("Archivo con posiciones de cierre abierto\n");
	}

	for(ulong eachBit=0; eachBit < bitsCount; eachBit++)
	{
		ulong esUnUno = es_un_uno(textUlong, eachBit);
		currentLevel = getCurrentLevel(eachBit, &statusNode, currentLevel, esUnUno);
		if(currentLevel > maxLevel)
			maxLevel = currentLevel;

		if(esUnUno)
		{
			totalTimeAllFC = 0;
			findCloseUnified(textUlong, bitsCount, currentLevel, givenLevel, eachBit, &posMyArrays, &fileResult, &totalTimeAllFC);

			//nivel nro_parentesis tiempo
			fprintf(fileSearchResult, "%d\t%d\t%.4f\n", currentLevel, eachBit, totalTimeAllFC);
		}
	}
	fclose(fileSearchResult);
	fclose(fileResult);
	printf("MAXIMO NIVEL: %d \n", maxLevel);
	printf("El tiempo total con el FindClose MEJORADO hasta el nivel: %d fue: %.4f ms \n", givenLevel , totalTimeAllFC);
}

/**
 * Saca las estadisticas pero solo usando el FindClose original, para poder compararlo con la corrida del modificado
 */
void getStatics_FindCloseOriginal(ulong *textUlong, ulong size, ulong bitsCount, char *fileNameOutput)
{
	ulong currentLevel = 0, cantNodos=0, cantHojas=0, eachPositionClose;
	ulong statusNode = 0; //0=cerrado, 1=abierto

	// >>>>>>>>>>>>>>> vbles para medir tiempo de ejecucion de findclose modificado y original.
		clock_t beginTimeAllFC, endTimeAllFC;
		double totalTimeAllFC = 0;
	// <<<<<<<<<<<<<<< FIN Vbles para medir tiempo de ejecucion de findclose y count.

	// Abrir el file con el resultado
	FILE *fileSearchResult;
	if((fileSearchResult=fopen(fileNameOutput,"w+"))==NULL)
	{
		printf("--------------------\n");
		printf("**Error: archivo %s no encontrado.\n",  fileNameOutput);
	}
	else{
		printf("Archivo de resultado del search abierto\n");
	}

	FILE *fileResult;
	if((fileResult=fopen("/home/jesica/Documents/tesis/ejecucion/results/solo_para_mi/cierres_original.txt","w+"))==NULL)
	{
		printf("--------------------\n");
		printf("**Error: archivo no encontrado\n");
	}
	else{
		printf("Archivo con posiciones de cierre abierto\n");
	}

	for(ulong eachBit=0; eachBit < bitsCount; eachBit++)
	{
		ulong esUnUno = es_un_uno(textUlong, eachBit);
		currentLevel = getCurrentLevel(eachBit, &statusNode, currentLevel, esUnUno);

		if(esUnUno)
		{
				beginTimeAllFC = clock();
			eachPositionClose = FindCloseOrig(textUlong, eachBit, bitsCount, &cantNodos, &cantHojas);
				endTimeAllFC = clock();
				totalTimeAllFC += (double)(endTimeAllFC - beginTimeAllFC);

			fprintf(fileResult, "%s%d\t%s%d\t%s%d\t%s%d\t%s%d\n", "Nivel:",currentLevel, "Posicion:",eachBit, "Cierra en= ",eachPositionClose, "Nodos= ", cantNodos, "Hojas= ", cantHojas);
			cantNodos = 0;
			cantHojas = 0;

			//File para grafica (datos: nivel nro_parentesis tiempo)
			fprintf(fileSearchResult, "%d\t%d\t%.4f\n", currentLevel, eachBit, totalTimeAllFC);
		}
	}
	fclose(fileSearchResult);
	fclose(fileResult);
	printf("El tiempo total con el FindClose ORIGINAL fue : %.4f  ms.\n", totalTimeAllFC);
}

int main(void) {
	/*puts("!!!Hello World!!!"); // prints !!!Hello World!!!
	return EXIT_SUCCESS;
	*/

	ulong bitsCount= 0;
	ulong *textUlong ;
	ulong sizeArray=0;
	char fileInputName[70], fileOutputOriginal[80], fileOutputModifiedBuilding[80], fileOutputModifiedSearch[80];
	ulong level = 3;


/* descomentar para probar si funciona, es un texto chico, conocido...
/// ----------------------------------------------------------
	unsigned char allText[5];
	allText[0] = 237; 	//11101101 = 128+64+32+0+8+4+0+1 =237
	allText[1] = 73; 	//01001001 = 0+64+0+0+8+0+0+1 = 73
	allText[2] = 166;	//10100110 = 128+0+32+0+0+4+2+0 = 166
	allText[3] = 181;	//10110101 = 128+0+32+16+0+4+0+1 = 181
	allText[4] = 0; 	//00000000 = 0

	// Convierto el unsigned char en unsigned long
	uchartoulong(allText, &textUlong, 36);
	level = 3;
	sizeArray = 5;
	bitsCount = 36;
/// ----------------------------------------------------------
*/


/* Lectura de toda la info de
 * 1-element: cantidad de elementos en el array
 * 2-level: nivel hasta el que debemos usar el findclose mejorado
 * 3-fileInput: nombre del archivo de entrada con los datos
 * 4-fileOutputOriginal: nombre del archivo de salida, que va a contener los datos de usar el findclose original para graficar y comparar con el uso del FC modificado
 * 5-fileOutputModifiedBuild: nombre del archivo de salida que contendra datos como resultado de la construccion de estructuras para el findClose mejorado
 * 6-fileOutputModifiedSearch: nombre del archivo de salida que contendra datos como resultado de usar el findclose mejorado para graficar y comparar con el FC original.
 */
	FILE * file, *fileInfo;
	if ((fileInfo=fopen("info.dat", "r+"))==NULL)
	{
		printf("--------------------\n");
		printf("**Error: archivo no encontrado\n");
		printf("--------------------\n\n\n");
	}
	else{
		fseek( fileInfo, 0L, SEEK_SET);
		fscanf(fileInfo, "# element=%u bits=%u level=%u fileInput=%s fileOutputOriginal=%s fileOutputModifiedBuild=%s fileOutputModifiedSearch=%s", &sizeArray, &bitsCount, &level, fileInputName, fileOutputOriginal, fileOutputModifiedBuilding, fileOutputModifiedSearch);
		textUlong = (ulong *) malloc(sizeof(ulong)*sizeArray);
	}

	// Leo el file con la info de entrada para ejecutar
	if ((file=fopen(fileInputName, "r+"))==NULL)
	{
		printf("--------------------\n");
		printf("**Error: archivo no encontrado\n");
		printf("--------------------\n\n\n");
	}
	else{
		fseek( file, 0L, SEEK_SET);
		fread(textUlong, sizeof(ulong), sizeArray, file);
	}

/////////////////////

	// Metodo de inicializacion necesarios para usar el FindClose Original (de Dario)
	initRankExcLeavesTables();
	initExcBitmapTables(textUlong, bitsCount);

	// Construccion de estructura para el FindClose Mejorado
	buildFindClose(textUlong, sizeArray, bitsCount, level, fileOutputModifiedBuilding);

	// Calculo de tiempos usando el FindClose unificado (original + mejorado, el original se usa para niveles superior al nivel pasado)
	// se debe llamar por cada linea del file donde cada linea tiene diferentes niveles dados
		printf("-----------------------------------------------------\n");
	getStatics(textUlong, sizeArray, bitsCount, level, fileOutputModifiedSearch);

	printf("-----------------------------------------------------\n");

	//saco las estadisticas del findClose original, pero esto lo tengo que hacer solo una vez
		getStatics_FindCloseOriginal(textUlong, sizeArray, bitsCount, fileOutputOriginal);


	/* otro texto chico
	unsigned char allText[8];
	allText[0] = 244;
	allText[1] = 181;
	allText[2] = 26;
	allText[3] = 122;
	allText[4] = 102;
	allText[5] = 134;
	allText[6] = 228;
	allText[7] = 0;
	findClose(allText, 8, 58);
*/

}
