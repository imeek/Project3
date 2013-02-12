
#include <fstream>
#include <iostream>
#include <iomanip>
#include <cmath>
#include <ctime>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

using namespace std;

#define SWAP(a,b) tempr=(a);(a)=(b);(b)=tempr
#define TAB '\t'

float pi = 4.0 * atan((double) 1);

/* like abs() but for doubles. necessary because */
/* abs() only accepts and returns ints */
float flabs(float f)	{
return f * (f<0? -1: 1);
}

/* returns the maximum value at a given bit-depth */
int depthMax(int bits)	{
return (int)pow(2.0, bits-1);
}

/* returns maximum value in an array of doubles */
float getMax(float *data, long captured_samples)	{
    double c, m;
    int i;
    for (i = 0, m = 0; i < captured_samples; ++i) 
    {
       c = flabs(data[i]);
       if (c > m)
         m = c;
    }
    return m;
}

/* www.strchr.com/standard_deviation_in_one_pass */
/* - this version takes two */
float std_dev1(float *data, int n) {
    if(n == 0)
        return 0.0;
    float sum = 0;
    for(int i = 0; i < n; ++i)
       sum += data[i];
    float mean = sum / n;
    float sq_diff_sum = 0;
    for(int i = 0; i < n; ++i) {
       float diff = data[i] - mean;
       sq_diff_sum += diff * diff;
    }
    float variance = sq_diff_sum / n;
    return sqrt(variance);
}

void quantisation(float *data, long captured_samples,float dataMax, int depthMax )	
{
    for(int i=0; i<captured_samples; i++)	
    {	
//        data[i]=data[i];
      data[i]= floor(depthMax*data[i]/dataMax);	
    }
}

void tone(float *data, int ndata, float freq, float delta, int nTseg) {
/* tone generation function */
  static double Tlast = 0.0;  
  if (nTseg == 0)
  {
    Tlast = 0.0;
  }
             
  for (int k = 0; k < ndata; k++) 
  {
      data[k] = sin(2 * M_PI * freq*(k * delta + Tlast));

  }
  Tlast += ndata*delta;
}

void four1(float data[], unsigned long nn, int isign)
/*******************************************************************************
Replaces data[1..2*nn] by its discrete Fourier transform, if isign is input as
1; or replaces data[1..2*nn] by nn times its inverse discrete Fourier transform,
if isign is input as -1. data is a complex array of length nn or, equivalently,
a real array of length 2*nn. nn MUST be an integer power of 2 (this is not
checked for!).
*******************************************************************************/
{
unsigned long n,mmax,m,j,istep,i;
double wtemp,wr,wpr,wpi,wi,theta;
float tempr,tempi;

n=nn << 1;
j=1;
for (i=1;i<n;i+=2) {	/* This is the bit-reversal section of the routine. */
if (j > i) {
SWAP(data[j],data[i]);	/* Exchange the two complex numbers. */
SWAP(data[j+1],data[i+1]);
}
m=n >> 1;
while (m >= 2 && j > m) {
j -= m;
m >>= 1;
}
j += m;
}
mmax=2;
while (n > mmax) {	/* Outer loop executed log2 nn times. */
istep=mmax << 1;
theta=isign*(6.28318530717959/mmax);	/* Initialize the trigonometric recurrence. */
wtemp=sin(0.5*theta);
wpr = -2.0*wtemp*wtemp;
wpi=sin(theta);
wr=1.0;
wi=0.0;
for (m=1;m<mmax;m+=2) {	/* Here are the two nested inner loops. */
for (i=m;i<=n;i+=istep) {
j=i+mmax;	/* This is the Danielson-Lanczos formula. */
tempr=wr*data[j]-wi*data[j+1];
tempi=wr*data[j+1]+wi*data[j];
data[j]=data[i]-tempr;
data[j+1]=data[i+1]-tempi;
data[i] += tempr;
data[i+1] += tempi;
}
wr=(wtemp=wr)*wpr-wi*wpi+wr;	/* Trigonometric recurrence. */
wi=wi*wpr+wtemp*wpi+wi;
}
mmax=istep;
}
}

void realft(float data[], unsigned long n, int isign)
/* Calculates the Fourier transform of a set of n real-valued data points. Replaces this data
(which is stored in array data(1:n)) by the positive frequency half of its complex Fourier
transform. The real-valued first and last components of the complex transform are returned
as elements data(1) and data(2), respectively. n must be a power of 2. This routine
also calculates the inverse transform of a complex data array if it is the transform of real
data. (Result in this case must be multiplied by 2/n.) */
/*
For a 1024-point real-valued input array, realft calculates the values of 513 complex points, corresponding to frequencies ranging from zero up to, and including, half the sampling frequency.
For zero-based notation, we can consider the transform points to be numbered 0 through 512, and here's the way realft puts their values into your array. 
(The imaginary components of the first and last transform points are equal to zero, so these values don't be needed to conveyed back to the calling program.)

x[0] --- real component of transform point 0
x[1] --- real component of transform point 512
x[2] --- real component of transform point 1
x[3] --- imaginary component of transform point 1
x[4] --- real component of transform point 2
x[5] --- imaginary component of transform point 2
.
.
.
x[1022] --- real component of transform point 511
x[1023] --- imaginary component of transform point 511
*/
{
void four1(float data[], unsigned long nn, int isign);
unsigned long i,i1,i2,i3,i4,np3;
float c1=0.5,c2,h1r,h1i,h2r,h2i;
double wr,wi,wpr,wpi,wtemp,theta;       // Double precision for the trigonometric recurrences.

theta=3.141592653589793/(double) (n>>1);        // Initialize the recurrence.
if (isign == 1) {
c2 = -0.5;
four1(data,n>>1,1);     // The forward transform is here.
} else {
c2=0.5;         // Otherwise set up for an inverse transform.
theta = -theta;
}
wtemp=sin(0.5*theta);
wpr = -2.0*wtemp*wtemp;
wpi=sin(theta);
wr=1.0+wpr;
wi=wpi;
np3=n+3;
for (i=2;i<=(n>>2);i++) {               // Case i=1 done separately below.
i4=1+(i3=np3-(i2=1+(i1=i+i-1)));
h1r=c1*(data[i1]+data[i3]);     // The two separate transforms are separated out of data.
h1i=c1*(data[i2]-data[i4]);
h2r = -c2*(data[i2]+data[i4]);
h2i=c2*(data[i1]-data[i3]);
data[i1]=h1r+wr*h2r-wi*h2i;     // Here they are recombined to form the true transform of the original real data.
data[i2]=h1i+wr*h2i+wi*h2r;
data[i3]=h1r-wr*h2r+wi*h2i;
data[i4] = -h1i+wr*h2i+wi*h2r;
wr=(wtemp=wr)*wpr-wi*wpi+wr;    // The recurrence.
wi=wi*wpr+wtemp*wpi+wi;
}
if (isign == 1) {
data[1] = (h1r=data[1])+data[2];        // Squeeze the first and last data together to get them all within the original array.
data[2] = h1r-data[2];
} else {
data[1]=c1*((h1r=data[1])+data[2]);
data[2]=c1*(h1r-data[2]);
four1(data,n>>1,-1);                    // This is the inverse transform for the case isign=-1.
}
}

int main() {
    cout.precision(6);
    cout.setf(ios::fixed | ios::showpoint);
    
    /* Simulation initialisation variables */
    unsigned long sample_rate = 150; //Msps
    unsigned long captured_samples = 1 << 10; //1024 samples
    
    // number of bits data is sampled
    int bits = 14;
   
    const int tsegments = 10;
    
    /* Noise parameters */
    const float Po = 1E-3; // Watts
    const float Vpp = 4; // Volts
    const float Vmax = 2; // Volts
    const float Rt = 50; // Ohms
    float Pfs = (Vmax*Vmax)/(2*Rt); // full scale Power
    float Noise_dBm = 0.0;
    float ADC_squared = 0.0; //to replace
    double Re1,Im1,Re2,Im2,ZRe,ZIm;
    int idx = 0;
    
    Noise_dBm = -260.0*log10(2.0)+10*log10(Pfs/Po);
    cout << "Noise_dBm :" << Noise_dBm << endl;
  // Noise_dBm +=log10(ADC_squared); //to replace
            
    /* Signal Parameters */
    //float *f = (float*) malloc((sample_rate/2) * sizeof (float));
    float delta = 1/(float)sample_rate;
    int depth = depthMax(bits);
    cout << "depth"<<TAB<<depth <<endl;
    int getmaxvalue = 0;
    double freq = 0.0;
    
    const int nf = 74;
    float N_dBm[5][nf];
    for (int l=0;l<nf;l++)
    {
        N_dBm[0][l] = 0.0;
        N_dBm[1][l] = 0.0;
        N_dBm[2][l] = 0.0;
        N_dBm[3][l] = 0.0;
        N_dBm[4][l] = 0.0;    
    }
    
    float N_Phi[5][nf];
    for (int l=0;l<nf;l++)
    {
        N_Phi[0][l] = 0.0;
        N_Phi[1][l] = 0.0;
        N_Phi[2][l] = 0.0;
        N_Phi[3][l] = 0.0;
        N_Phi[4][l] = 0.0;    
    }
    
    
  //  double fft_length; 
    float Tseg[tsegments];
    float Tseg2[tsegments];
    
    
    for (int n=0 ;n<5 ;n++ )
    {
      
      //  fft_length = pow ( 2.0,(10+n) );
        captured_samples = 1 << (10+n);
        
        /* Simulation frequency */
        freq = 0.0;
        float *data = (float*) malloc((captured_samples) * sizeof (float));
        float *data2 = (float*) malloc((captured_samples) * sizeof (float));
        for (int j=0 ;j<nf ;j++ )
        {
            
            cout<< " freq :"<< freq <<endl;
            
            for (int t=0 ;t<tsegments ;t++ )
            {
                /* Simulation data vectors */
                
                
                /* Generate Signal */
                tone(data, captured_samples, freq, delta, t);
                tone(data2, captured_samples, freq, delta, t);
               // getmaxvalue = getMax(data,captured_samples);
                /* Quantise Data*/
                
                quantisation(data, captured_samples, 1 , depth );

                /*Window data*/
             
                data[0] = 0.0;
                for(int k = 1 ; k < captured_samples/2; k++) 
                {
                    data[k] *= 2.0*(float)k/captured_samples;
                    data[captured_samples - k] *= 2.0*(float)k/captured_samples;
                }
                
                /* FFT data */
                realft(data-1, captured_samples, 1);
                realft(data2-1, captured_samples, 1);
                
                /* Normalise FFT data */
                for(int k = 0.0; k< captured_samples; k++)
                {
                  data[k] *= sqrt(2.0)/captured_samples;
                  data2[k] *= sqrt(2.0)/captured_samples;
                }
                /* Output simulation results to data array */
                if (freq == 0.0)
                {
                  Re1 = data[0];
                  Im1 = 0.0;
                  Re2 = data2[0];
                  Im2 = 0.0;
                }
                else 
                {
                  idx = (int)trunc(freq/sample_rate*captured_samples);
               //   cout << " idx  " << TAB << idx <<endl; 
                  Re1 = data[2*idx];
                  Im1 = data[2*idx+1];
                  Re2 = data2[2*idx];
                  Im2 = data2[2*idx+1]; 
                }
                
                
                
                ZRe = Re1*Re2 + Im1*Im2;
                ZIm = Im1*Re2 - Re1*Im2;
                if (freq == 0.0)
                {
                 cout << " ZRe " << TAB << ZRe <<endl; 
                 cout << " ZIm " << TAB << ZIm <<endl;
                }
                
                Tseg[t] = sqrt(ZRe*ZRe+ZIm*ZIm);
                
                Tseg2[t] = atan2(ZIm, ZRe); 
                
                //Tseg[t] = sqrt(data[2*idx+1]*data[2*idx+1]+data[2*idx]*data[2*idx]);
                //Tseg2[t] = sqrt(data[2*idx+1]*data[2*idx+1]+data[2*idx]*data[2*idx]);
              }
           
            // cout << "  " << TAB << <<endl; 
            // cout << "  " << TAB << <<endl;
            
            N_dBm[n][j] = log10( std_dev1(Tseg, tsegments)) + Noise_dBm;
            N_Phi[n][j] = std_dev1(Tseg2, tsegments); 
            
            freq = freq + 1;
            /* */
        } 
        /* delete data vectors */
        free(data);
        free(data2);
    }    
   // cout << "  freq" << TAB <<freq <<endl;  
    freq = 0.0;
    ofstream dBm_out("dBm_out.dat");
    ofstream Phi_out("Phi_out.dat");
    for (int l=0;l<nf;l++)
    {
        
        dBm_out << freq << TAB << N_dBm[0][l] << TAB << N_dBm[1][l] << TAB << N_dBm[2][l] << TAB << N_dBm[3][l] << TAB << N_dBm[4][l] << endl;
        Phi_out << freq << TAB << N_Phi[0][l] << TAB << N_Phi[1][l] << TAB << N_Phi[2][l] << TAB << N_Phi[3][l] << TAB << N_Phi[4][l] << endl;
        freq = freq + 1;
    }
    dBm_out.close();
    Phi_out.close();
    
    
    
    return 0;
}

