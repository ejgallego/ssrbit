#include <time.h>
#include <stdio.h>
#include <stdlib.h>

int max = 16;

int solutions[] = { 1, 0, 0, 2, 10, 4, 40, 92, 352, 724, 
                    2680, 14200, 73712, 365596, 2279184, 14772512,
                    95815104, 666090624 };

// Code from Jean-Christophe Filliâtre, "Verifying two lines of C with
// Why3: an exercise in program verification".

int t(int a, int b, int c) 
{
  int d, e=a&~b&~c, f=1;
  if (a) {
    for (f=0; d=e&-e; e-=d){
      f += t(a-d,(b+d)*2,(c+d)/2);
    }
  }
  return f;
}

int queens(int n) 
{
  return t(~(~0<<n),0,0);
}

// From: [https://www.guyrutenberg.com/2007/09/22/profiling-code-using-clock_gettime/]
struct timespec diff(struct timespec start, struct timespec end)
{
  struct timespec temp;
  if ((end.tv_nsec-start.tv_nsec)<0) {
    temp.tv_sec = end.tv_sec-start.tv_sec-1;
    temp.tv_nsec = 1000000000+end.tv_nsec-start.tv_nsec;
  } else {
    temp.tv_sec = end.tv_sec-start.tv_sec;
    temp.tv_nsec = end.tv_nsec-start.tv_nsec;
  }
  return temp;
}

int main()
{

  struct timespec ts_start;
  struct timespec ts_end;


  FILE *fp = fopen("queens_c.dat", "w");
  if (!fp) {
    fprintf(stderr, "Cannot open data file\n");
    exit(1);
  }

  for (int i = 1; i <= max; i++){
    clock_gettime(CLOCK_MONOTONIC, &ts_start);
    int solution = queens(i);
    clock_gettime(CLOCK_MONOTONIC, &ts_end);
    struct timespec time = diff(ts_start, ts_end); 
    double t = (double) time.tv_sec * 1000.0 + (double)time.tv_nsec / 1000000.0;
    printf("%d queens: %lf ms.\n", i, t);
    fprintf(fp, "%d\t%lf\n", i, t);
    if (solutions[i-1] != solution){
      printf("Invalid result!\n");
      exit(1);
    }
  }
  return 0;
}
