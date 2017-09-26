//rs code
//m=8

#include <math.h>
#include <stdio.h>
#include <string.h>

#define mm  8          /* RS code over GF(2**4) - change to suit */
#define nn  255          /* nn=2**mm -1   length of codeword */
#define tt  10           /* number of errors that can be corrected */
#define kk  235           /* kk = nn-2*tt  */

int pp[mm+1] = {1, 0, 1, 1, 1, 0, 0, 0, 1};
int alpha_to [nn+1], index_of [nn+1], gg [nn-kk+1] ;
int recd [nn], data [kk], bb [nn-kk] ;


//generate_gf modify by local
void generate_gf()
/* 生成GF(2^m)空间 */
{
	register int i, mask ;
	mask = 1 ;
	alpha_to[mm] = 0 ;
	for (i=0; i<mm; i++)
	{	
		alpha_to[i] = mask ;
		index_of[alpha_to[i]] = i ;
		if (pp[i]!=0)
			alpha_to[mm] ^= mask ;
		mask <<= 1 ;
	}
	index_of[alpha_to[mm]] = mm ;
	mask >>= 1 ;
	for (i=mm+1; i<nn; i++)
	{	
		if (alpha_to[i-1] >= mask)
			alpha_to[i] = alpha_to[mm] ^ ((alpha_to[i-1]^mask)<<1) ;
		else 
			alpha_to[i] = alpha_to[i-1]<<1 ;
		index_of[alpha_to[i]] = i ;
	}
	index_of[0] = -1 ;
	//alpha_to[nn] = 1;
	for(i=0;i<mm;i++)
		printf("gf(%d) is %d\n",i,alpha_to[i]);
}

void gen_poly()
/* 生成---生成多项式*/
{
	register int i,j ;
	gg[0] = 2 ;    /* primitive element alpha = 2  for GF(2**mm)  */
	gg[1] = 1 ;    /* g(x) = (X+alpha) initially */
	for (i=2; i<=nn-kk; i++)
    {
		gg[i] = 1 ;
		for (j=i-1; j>0; j--)
			if (gg[j] != 0)  
				gg[j] = gg[j-1]^ alpha_to[(index_of[gg[j]]+i)%nn];
			else 
				gg[j] = gg[j-1] ;
		gg[0] = alpha_to[(index_of[gg[0]]+i)%nn] ;     /* gg[0] can never be zero */
   }
   //printf("polynomial:\n");
   //for(i=0; i<=nn-kk; i++)
	//   printf("%d      ", gg[i]);
   //printf("\n");
   /* convert gg[] to index form for quicker encoding */
   for (i=0; i<=nn-kk; i++)  
	   gg[i] = index_of[gg[i]];

   //printf("polynomial:\n");
   //for(i=0; i<=nn-kk; i++)
	//   printf("%d      ", gg[i]);
   //printf("\n");
}

void encode_rs()
/* 编码*/
{
	register int i,j ;
	int feedback ;
	for (i=0; i<nn-kk; i++)   bb[i] = 0 ;
	for (i=kk-1; i>=0; i--)
    {
		//逐步的将下一步要减的，存入bb(i)
		feedback = index_of[data[i]^bb[nn-kk-1]] ;
		if(feedback != -1)
        {
			for (j=nn-kk-1; j>0; j--)
            if (gg[j] != -1)
				bb[j] = bb[j-1]^alpha_to[(gg[j]+feedback)%nn] ;		//plus = ^
            else
				bb[j] = bb[j-1] ;
			bb[0] = alpha_to[(gg[0]+feedback)%nn] ;
        }
		else
        {
			for (j=nn-kk-1; j>0; j--)
				bb[j] = bb[j-1] ;
			bb[0] = 0 ;
        };
    };
}

void decode_rs()
 {/*解码*/
	register int i,j,u,q ;
	int elp[nn-kk+2][nn-kk], d[nn-kk+2], l[nn-kk+2], u_lu[nn-kk+2], s[nn-kk+1] ;
	int count=0, syn_error=0, root[tt], loc[tt], z[tt+1], err[nn], reg[tt+1] ;
/* first form the syndromes */
	for(i=0; i<nn; i++) //转换成GF空间的alpha幂次
		if(recd[i] == -1)
			recd[i] = 0;
		else
			recd[i] = index_of[recd[i]];

	for (i=1; i<=nn-kk; i++)
	{
		s[i] = 0 ;
		for (j=0; j<nn; j++)
        if (recd[j]!=-1)
			s[i] ^= alpha_to[(recd[j]+i*j)%nn] ;      /* recd[j] in index form */
								/* convert syndrome from polynomial form to index form  */
		if (s[i]!=0)  
			syn_error=1 ;        /* set flag if non-zero syndrome => error */
		printf("%3d", s[i]);
		s[i] = index_of[s[i]] ;
		printf("%3d", s[i]);
    } ;
	if (syn_error)       /* if errors, try and correct */
    {printf("*\n");
/* compute the error location polynomial via the Berlekamp iterative algorithm,
   following the terminology of Lin and Costello :   d[u] is the 'mu'th
   discrepancy, where u='mu'+1 and 'mu' (the Greek letter!) is the step number
   ranging from -1 to 2*tt (see L&C),  l[u] is the
   degree of the elp at that step, and u_l[u] is the difference between the
   step number and the degree of the elp.*/
/* initialise table entries */
		d[0] = 0 ;           /* index form */
		d[1] = s[1] ;        /* index form */
		elp[0][0] = 0 ;      /* index form */
		elp[1][0] = 1 ;      /* polynomial form */
		for (i=1; i<nn-kk; i++)
        {	
			elp[0][i] = -1 ;   /* index form */
			elp[1][i] = 0 ;   /* polynomial form */
        }
		l[0] = 0 ;
		l[1] = 0 ;
		u_lu[0] = -1 ;
		u_lu[1] = 0 ;
		u = 0 ;
		do
		{
			u++ ;
			if (d[u]==-1)
			{ 
				l[u+1] = l[u] ;
				for (i=0; i<=l[u]; i++)
				{  
					elp[u+1][i] = elp[u][i] ;
					elp[u][i] = index_of[elp[u][i]] ;
				}
			}
			else
/* search for words with greatest u_lu[q] for which d[q]!=0 */
			{ 
				q = u-1 ;
				while ((d[q]==-1) && (q>0)) 
					q-- ;
/* have found first non-zero d[q]  */
				if (q>0)
				{ 
					j=q ;
				do
				{ 
					j-- ;
					if ((d[j]!=-1) && (u_lu[q]<u_lu[j]))
					q = j ;
				}while (j>0) ;
             } ;
/* have now found q such that d[u]!=0 and u_lu[q] is maximum */
/* store degree of new elp polynomial */
            if (l[u]>l[q]+u-q)  
				l[u+1] = l[u] ;
            else  
				l[u+1] = l[q]+u-q ;
/* form new elp(x) */
            for (i=0; i<nn-kk; i++)    
				elp[u+1][i] = 0 ;
            for (i=0; i<=l[q]; i++)
				if (elp[q][i]!=-1)
					elp[u+1][i+u-q] = alpha_to[(d[u]+nn-d[q]+elp[q][i])%nn] ;
            for (i=0; i<=l[u]; i++)
              { 
				  elp[u+1][i] ^= elp[u][i] ;
                elp[u][i] = index_of[elp[u][i]] ;  /*convert old elp value to index*/
              }
		}
		u_lu[u+1] = u-l[u+1] ;
/* form (u+1)th discrepancy */
        if (u<nn-kk)    /* no discrepancy computed on last iteration */
		{
			if (s[u+1]!=-1)
				d[u+1] = alpha_to[s[u+1]] ;
            else
				d[u+1] = 0 ;
            for (i=1; i<=l[u+1]; i++)
				if ((s[u+1-i]!=-1) && (elp[u+1][i]!=0))
					d[u+1] ^= alpha_to[(s[u+1-i]+index_of[elp[u+1][i]])%nn] ;
            d[u+1] = index_of[d[u+1]] ;    /* put d[u+1] into index form */
		}
	} while ((u<nn-kk) && (l[u+1]<=tt)) ;
	u++ ;
	if (l[u]<=tt)         /* can correct error */
	{
/* put elp into index form */
		for (i=0; i<=l[u]; i++)   
			elp[u][i] = index_of[elp[u][i]] ;
/* find roots of the error location polynomial */
		/*求错误位置多项式的根*/
		for (i=1; i<=l[u]; i++)
			reg[i] = elp[u][i] ;
		count = 0 ;
		for (i=1; i<=nn; i++)
		{  
			q = 1 ;
			for (j=1; j<=l[u]; j++)
			if (reg[j]!=-1)
			{ 
				reg[j] = (reg[j]+j)%nn ;
				q ^= alpha_to[reg[j]] ;
			} ;
			if (!q)        /* store root and error location number indices */
			{ 
				root[count] = i;
				loc[count] = nn-i ;
				count++ ;
				printf("根%d=%d\n", q, nn-i);
			};
		} ;
		if (count==l[u])    /* no. roots = degree of elp hence <= tt errors */
		{/* form polynomial z(x) */
			for (i=1; i<=l[u]; i++)        /* Z[0] = 1 always - do not need */
            { 
				if ((s[i]!=-1) && (elp[u][i]!=-1))
					z[i] = alpha_to[s[i]] ^ alpha_to[elp[u][i]] ;
				else if ((s[i]!=-1) && (elp[u][i]==-1))
					z[i] = alpha_to[s[i]] ;
				else if ((s[i]==-1) && (elp[u][i]!=-1))
					z[i] = alpha_to[elp[u][i]] ;
				else
					z[i] = 0 ;
				for (j=1; j<i; j++)
					if ((s[j]!=-1) && (elp[u][i-j]!=-1))
						z[i] ^= alpha_to[(elp[u][i-j] + s[j])%nn] ;
				z[i] = index_of[z[i]] ;         /* put into index form */
            } ;
  /* evaluate errors at locations given by error location numbers loc[i] */
			/*计算错误图样*/
			for (i=0; i<nn; i++)
			{ 
				err[i] = 0 ;
				if (recd[i]!=-1)        /* convert recd[] to polynomial form */
					recd[i] = alpha_to[recd[i]] ;
				else  
					recd[i] = 0 ;
             }
			for (i=0; i<l[u]; i++)    /* compute numerator of error term first */
            { 
				err[loc[i]] = 1;       /* accounts for z[0] */
				for (j=1; j<=l[u]; j++)
					if (z[j]!=-1)
						err[loc[i]] ^= alpha_to[(z[j]+j*root[i])%nn] ;
				if (err[loc[i]]!=0)
				{ 
					err[loc[i]] = index_of[err[loc[i]]] ;
					q = 0 ;     /* form denominator of error term */
					for (j=0; j<l[u]; j++)
					if (j!=i)
						q += index_of[1^alpha_to[(loc[j]+root[i])%nn]] ;
					q = q % nn ;
					err[loc[i]] = alpha_to[(err[loc[i]]-q+nn)%nn] ;
					recd[loc[i]] ^= err[loc[i]] ;  /*recd[i] must be in polynomial form */
				}
			}
		}
		else    /* no. roots != degree of elp => >tt errors and cannot solve */
		{	/*错误太多，无法更正*/
			for (i=0; i<nn; i++)        /* could return error flag if desired */
				if (recd[i]!=-1)        /* convert recd[] to polynomial form*/
					recd[i] = alpha_to[recd[i]] ;
				else  
					recd[i] = 0 ;     /* just output received codeword as is */
		}
		}
		else         /* elp has degree has degree >tt hence cannot solve */
		{	/*错误太多，无法更正*/
			for (i=0; i<nn; i++)       /* could return error flag if desired */
				if (recd[i]!=-1)        /* convert recd[] to polynomial form */
					recd[i] = alpha_to[recd[i]] ;
				else  
					recd[i] = 0 ;     /* just output received codeword as is */
		}
	}
	else       /* no non-zero syndromes => no errors: output received codeword */
		for (i=0; i<nn; i++)
		{
			if (recd[i]!=-1)        /* convert recd[] to polynomial form */
				recd[i] = alpha_to[recd[i]] ;
			else  
				recd[i] = 0 ;
			//printf("*");
		}

 }

int main()
{
	int i, length;
	char strSrc[255], strDst[255];
	printf("input strSrc :\n");
	scanf("%s", strSrc);
	length = strlen(strSrc);
	if(length <= 0)
		return 0;

	generate_gf();
	printf("Look-up tables for GF(2**%2d)\n",mm) ;
	printf("  i   alpha_to[i]  index_of[i]\n") ;
	for (i=0; i<=nn; i++)
		printf("%3d      %3d          %3d\n",i,alpha_to[i],index_of[i]);
	printf("\n\n");

	gen_poly();

	for(i=0; i<kk; i++)
		data[i] = 0;

	/* for example, say we transmit the following message (nothing special!) */
	//for(i=0; i<length; i++)
	//	data[i] = strSrc[i];
	data[0] = 8 ;
	data[1] = 6 ;
	data[2] = 8 ;
	data[3] = 1 ;
	data[4] = 2 ;
	data[5] = 4 ;
	data[6] = 15 ;
	data[7] = 9 ;
	data[8] = 55 ;

	encode_rs();

	data[0] = 19 ;
    data[1]=32;
	for (i=0; i<nn-kk; i++)  
		recd[i] = bb[i] ;
	for (i=0; i<kk; i++) 
		recd[i+nn-kk] = data[i] ;


/*	printf("Results for Reed-Solomon code (n=%3d, k=%3d, t= %3d)\n\n",nn,kk,tt) ;
	printf("  i  data[i]   recd[i](decoded)   (data, recd in polynomial form)\n");
	for (i=0; i<nn-kk; i++)
		printf("%3d    %3d      %3d\n",i, bb[i], recd[i]) ;
	for (i=nn-kk; i<=nn; i++)
		printf("%3d    %3d      %3d\n",i, data[i-nn+kk], recd[i]) ;*/

	decode_rs() ; 

	printf("Results for Reed-Solomon code (n=%3d, k=%3d, t= %3d)\n\n",nn,kk,tt) ;
	printf("  i  data[i]   recd[i](decoded)   (data, recd in polynomial form)\n");
	for (i=0; i<nn-kk; i++)
		printf("%3d    %3d      %3d\n",i, bb[i], recd[i]) ;
	for (i=nn-kk; i<=nn; i++)
	{
		printf("%3d    %3d      %3d\n",i, data[i-nn+kk], recd[i]) ;
	}
	for(i=0; i<length; i++)
		strDst[i] = recd[i+nn-kk];
	strDst[length] = '\0';
	printf("%s\n", strDst);
}
