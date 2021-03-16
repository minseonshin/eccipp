// gcc -o eccipp-d eccipp-d.c && time ./eccipp-d {dimensions of projective spaces}
// Euler Characteristics of Complete Intersections in Products of Projective space
// for a Brauer class which is n-torsion, consider the n-fold product of P^(n-1); then the classes that descend will be O( e_1 , ... , e_n ) where e_1 + ... + e_n = 0 (mod n)

#include <stdio.h>
#include <stdlib.h>

typedef long long int ll;

#define min(x,y) (((x)<(y)) ? (x):(y))
#define max(x,y) (((x)>(y)) ? (x):(y))
#define PTL 60 // pascal's triangle limit (i.e. how many rows to compute)
#define sgn(n) (((n+1)%2)*2-1) // 1 if n = 0 (mod 2), -1 if n = 1 (mod 2)
#define CRFLAG 0 // with or without the congruence relation?

ll **pt; // pascal's triangle -- pt[n][k] = binomial(n,k)

ll MR, MC;          // number of rows (#proj spaces), columns (#divisors) in the matrix of multidegrees
ll IND;             // index of the Brauer-Severi variety (usually psd[i] + 1)
ll *psd, totd;      // projective space dimensions, total dimension
ll **me;            // current matrix of multidegrees under consideration
ll *whc;            // which indices in {0 , ... , MC-1} (columns) are included?
ll *bnn, *bnk;      // will compute binomial(bnn[0],bnk[0]) * ... * binomial(bnn[MR-1],bnn[MR-1])
ll ans, nic;        // number of included columns
ll **mdid;          // all possible multidegrees
ll didcount;        // global count of mdid computed so far
ll *mte;            // current multidegree under consideration
ll IDC;             // how many invariant divisors are there?
ll MAXMTE;          // maximum value of the components of each multidegree
ll *whr;            // which rows to include (for check_nonempty())
ll cmcsf;           // how many matrices checked so far (just for printing progress of enumeration)
ll **ards;          // array displaying distinctness of multidegrees
ll **dcd;            // degree of the canonical divisor

// binomial coefficients for any integer n (k >= 0)
// bn(n,k) = n(n-1) ... (n-k+1) / k!
ll bn(ll n, ll k){
	if(k <= n){return(pt[n][k]);}
	if(0 <= n && n < k){return(0);}
	if(n < 0){return(sgn(k)*pt[-n+k-1][k]);} // (-1)^k
}

// compute the euler characteristic, given matrix entries, and store in "ans"
// choose, at each step, whether to include that column
void compute_euler_char(ll c){
	ll i, mans;
	if(c == MC){
		mans=1;
		for(i=0;i<MR;i++){mans*=bn(bnn[i],bnk[i]);}
		ans += sgn(nic)*mans;
		return;
	}
	// do not include column c
	whc[c]=0; compute_euler_char(c+1);
	// include column c
	nic++; for(i=0;i<MR;i++){bnn[i] -= me[c][i];}
	whc[c]=1; compute_euler_char(c+1);
	nic--; for(i=0;i<MR;i++){bnn[i] += me[c][i];}
}

// print the matrix of multidegrees of divisors
void print_mat(ll c){
	ll i,j;
	printf("\n---- ");for(i=0;i<c;i++){printf("%2lld",i);} printf("\n");
	for(i=0;i<MR;i++){
		printf("P^%lld | ",psd[i]);
		for(j=0;j<c;j++){
			if(me[j][i] == 0){printf(". ");}
			else{printf("%lld ",me[j][i]);}
		}
		printf("\n");
	}
}

// checks that the intersections are nonempty
ll check_nonempty(ll r, ll c){
	ll i, j, nrc, td, a1=1, a2=1; // nrc = nonrestrictable columns, td = total dimension (of subproduct)
	if(r == MR){
		nrc=0;
		for(j=0;j<c;j++){
			for(i=0;i<MR;i++){
				if(whr[i] == 0 && me[j][i] != 0){break;}
			}
			if(i==MR){nrc++;}
		}
		td = 0; for(i=0;i<MR;i++){if(whr[i] == 1){td+=psd[i];}}
		if(td != 0 && td <= nrc){ return(0); }
		else{                     return(1); }
	}
	if(me[c-1][r] == 0){whr[r] = 0; a1 = check_nonempty(r+1,c);}
	if(a1 == 1        ){whr[r] = 1; a2 = check_nonempty(r+1,c);}
	return(a1*a2);
}

// enumerate mdid
// flag 0 = count
// flag 1 = enumerate
void cidcmdid(ll r, ll ssf, ll mflag){
	ll i, j, s;
	i = didcount;
	if(r == MR){
		s=0; for(j=0;j<MR;j++){ s+= mte[j];} if(s==1){return;}
		if(ssf != 0 && (CRFLAG == 0 || ssf == IND)){
			if(mflag == 0){ IDC++; }
			if(mflag == 1){ for(j=0;j<MR;j++){ mdid[didcount][j] = mte[j];} didcount++; }
		}
		return;
	}
	for(mte[r]=0;mte[r]<=MAXMTE && (mflag==0 || didcount < IDC);mte[r]++){
		cidcmdid(r+1,ssf+(IND/(psd[r]+1))*mte[r],mflag);
	}
}

// fill out the matrix entries and compute
void f(ll lastusedi, ll c){
	ll i,j, r, mf, mys, mym;
	if(c == MC){
		for(i=0;i<MR;i++){bnn[i] = psd[i]; bnk[i] = psd[i];}
		ans=0;
		nic=0;
		compute_euler_char(0);
		//cmcsf++; if(cmcsf%100000 == 0){for(j=0;j<MC;j++){for(i=0;i<MR;i++){printf("%lld",me[j][i]);}printf(" ");}printf("\n");}
		/*
		// check for "all 0s except two 1s"
		for(i=0;i<MR;i++){
			mys = 0; mym = 0;
			for(j=0;j<MC;j++){mys += me[j][i]; mym = max(mym,me[j][i]);}
			if(mys == psd[i] && mym == 1){return;}
		}
		*/
		if(ans == 0){
			print_mat(c);
		}
		return;
	}
	//if(c < 10){for(r=0;r<MR;r++){me[c][r] = 0;}me[c][MR-1-(c/(MR-3))] = 1; f(0,c+1); return; }
	for(i=lastusedi;i<IDC;i++){
		// set the cth column
		for(r=0;r<MR;r++){me[c][r] = mdid[i][r];}
		// check that the canonical bundle is not (anti-)ample
		if(c == 0){for(r=0;r<MR;r++){dcd[c][r] = psd[r]+1 - me[c][r];}}
		if(c >= 1){for(r=0;r<MR;r++){dcd[c][r] = dcd[c-1][r] - me[c][r];}}
		//for(r=0;r<MR;r++){if(dcd[c][r] >= 0){break;}} if(r == MR){continue;} // quit if all degrees are negative
		for(r=0;r<MR;r++){if(dcd[c][r] < 0){break;}} if(r != MR){continue;} // quit if one degree is negative
		// ensure that intersections are nonempty
		if(check_nonempty(0,c+1) == 0){continue;}
		// remove some redundancies (permutation of rows)
		if(c == 0){ 
			for(r=1;r<MR;r++){if(psd[r-1] == psd[r] && me[c][r-1] > me[c][r]){break;}}
			if(r < MR){continue;}
			ards[c][0] = 0;
			for(r=1;r<MR;r++){
				if(psd[r-1] == psd[r] && me[c][r-1] == me[c][r]){ards[c][r] = ards[c][r-1];}
				else{ards[c][r] = ards[c][r-1]+1;}
			}
		}
		if(c >= 1){
			for(r=1;r<MR;r++){if(ards[c-1][r-1] == ards[c-1][r] && me[c][r-1] > me[c][r]){break;}}
			if(r < MR){continue;}
			ards[c][0] = 0;
			for(r=1;r<MR;r++){
				if(ards[c-1][r-1] == ards[c-1][r] && me[c][r-1] == me[c][r]){ards[c][r] = ards[c][r-1];}
				else{ards[c][r] = ards[c][r-1]+1;}
			}
		}
		//if(c < 3){print_mat(c+1);}
		f(i,c+1);
	}
}

// Computes gcd(i,j)
ll gcd(ll i, ll j){
	while(i > 0 && j > 0){
		if(i >= j){i=i%j;}
		else{j=j%i;}
	}
	if(i == 0)return j;
	else if (j == 0) return i;
}

int main ( int argc , char ** argv ) {
	ll i, j;

	// enter dimensions of the projective spaces
	MR  = (ll) argc-1;
	psd = (ll*) malloc(MR*sizeof(ll)); for(i=0;i<MR;i++){psd[i] = (ll) atoi(argv[i+1]);} // psd[i] = MR-1;
	
	IND = 1; for(i=0;i<MR;i++){IND = (IND*(psd[i]+1))/(gcd(IND,psd[i]+1));}
	MC = -1; for(i=0;i<MR;i++){MC += psd[i];}
	MAXMTE = IND;
	printf("Index = %lld; taking ",IND);
	for(i=0;i<MR;i++){printf("P^%lld",psd[i]);if(i+1 < MR){printf("x");}}
	printf("; c=%lld divisors; maximum degree %lld\n",MC,MAXMTE);

	// allocate memory
	totd = 0; for(i=0;i<MR;i++){totd += psd[i];} //for(i=0;i<MR;i++){printf("%lld\n",psd[i]);}
	me = (ll**) malloc(MC*sizeof(ll)); for(j=0;j<MC;j++){me[j] = (ll*) malloc(MR*sizeof(ll));}
	whc = (ll*) malloc(MC*sizeof(ll));
	whr = (ll*) malloc(MR*sizeof(ll));
	bnn = (ll*) malloc(MR*sizeof(ll));
	bnk = (ll*) malloc(MR*sizeof(ll));
	mte = (ll*) malloc(MR*sizeof(ll));
	IDC = 0; cidcmdid(0,0,0);
	mdid = (ll**) malloc(IDC*sizeof(ll)); for(i=0;i<IDC;i++){mdid[i] = (ll*) malloc(MR*sizeof(ll));}
	ards = (ll**) malloc(MC*sizeof(ll)); for(j=0;j<MC;j++){ards[j] = (ll*) malloc(MR*sizeof(ll));}
	dcd  = (ll**) malloc(MC*sizeof(ll)); for(j=0;j<MC;j++){dcd[j] = (ll*) malloc(MR*sizeof(ll)); for(i=0;i<MR;i++){dcd[j][i] = 0;}}

	// compute binomial coefficients
	pt = (ll**) malloc(PTL*sizeof(ll*));
	for(i=0;i<PTL;i++){	pt[i] = (ll*) malloc((i+1)*sizeof(ll)); }
	for(i=0;i<PTL;i++){
		pt[i][0] = 1; pt[i][i] = 1;
		for(j=1;j<i;j++){ pt[i][j] = pt[i-1][j] + pt[i-1][j-1]; }
	}

	// compute mdid
	didcount = 0;
	cidcmdid(0,0,1);
	//printf("Here are multidegrees of divisors that descend:\n"); for(i=0;i<IDC;i++){printf("i=%lld [ ",i); for(j=0;j<MR;j++){printf("%lld ",mdid[i][j]);}printf("]\n");}

	// start computation
	cmcsf = 0;
	f(0,0);
}
