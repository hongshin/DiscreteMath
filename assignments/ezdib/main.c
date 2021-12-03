
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include "ezdib.h"

int bar_graph( HEZDIMAGE x_hDib, HEZDFONT x_hFont, int x1, int y1, int x2, int y2,
			   int nDataType, void *pData, int nDataSize, int *pCols, int nCols )
{
	int i, c, w, h;
	int tyw = 0, bw = 0;
	double v, dMin, dMax, dRMin, dRMax;

	// Sanity checks
	if ( !pData || 0 >= nDataSize || !pCols || !nCols )
		return 0;

	// Get the range of the data set
	ezd_calc_range( nDataType, pData, nDataSize, &dMin, &dMax, 0 );

	// Add margin to range
	dRMin = dMin - ( dMax - dMin ) / 10;
	dRMax = dMax + ( dMax - dMin ) / 10;

	if ( x_hFont )
	{	
		char num[ 256 ] = { 0 };
		
		// Calculate text width of smallest value
		sprintf( num, "%.2f", dMin );
		ezd_text_size( x_hFont, num, -1, &tyw, &h );
		ezd_text( x_hDib, x_hFont, num, -1, x1, y2 - ( h * 2 ), *pCols );

		// Calculate text width of largest value
		sprintf( num, "%.2f", dMax );
		ezd_text_size( x_hFont, num, -1, &w, &h );
		ezd_text( x_hDib, x_hFont, num, -1, x1, y1 + h, *pCols );
		if ( w > tyw )
			tyw	= w;
			
		// Text width margin
		tyw += 10;
	
	} // end if

	// Draw margins
	ezd_line( x_hDib, x1 + tyw - 2, y1, x1 + tyw - 2, y2, *pCols );
	ezd_line( x_hDib, x1 + tyw - 2, y2, x2, y2, *pCols );

	// Calculate bar width
	bw = ( x2 - x1 - tyw - nDataSize * 2 ) / nDataSize;

	// Draw the bars
	c = 0;
	for ( i = 0; i < nDataSize; i++ )
	{
		if ( ++c >= nCols )
			c = 1;

		// Get the value for this element
		v = ezd_scale_value( i, nDataType, pData, dRMin, dRMax - dRMin, 0, y2 - y1 - 2 );

		// Fill in the bar
		ezd_fill_rect( x_hDib, x1 + tyw + i + ( ( bw + 1 ) * i ), y2 - (int)v - 2,
							   x1 + tyw + i + ( ( bw + 1 ) * i ) + bw, y2 - 2, pCols[ c ] );

		// Outline the bar
		ezd_rect( x_hDib, x1 + tyw + i + ( ( bw + 1 ) * i ), y2 - (int)v - 2,
						  x1 + tyw + i + ( ( bw + 1 ) * i ) + bw, y2 - 2, *pCols );
	} // end for

	return 1;
}

#define PI		( (double)3.141592654 )
#define PI2		( (double)2 * PI )

int pie_graph( HEZDIMAGE x_hDib, int x, int y, int rad,
			   int nDataType, void *pData, int nDataSize, int *pCols, int nCols )
{
	int i, c;
	double v, pos, dMin, dMax, dTotal;

	// Sanity checks
	if ( !pData || 0 >= nDataSize || !pCols || !nCols )
		return 0;

	// Draw chart outline
	ezd_circle( x_hDib, x, y, rad, *pCols );

	// Get the range of the data set
	ezd_calc_range( nDataType, pData, nDataSize, &dMin, &dMax, &dTotal );

	// Draw the pie slices
	pos = 0; c = 0;
	ezd_line( x_hDib, x, y, x + rad, y, *pCols );
	for ( i = 0; i < nDataSize; i++ )
	{
		if ( ++c >= nCols )
			c = 1;

		// Get the value for this element
		v = ezd_scale_value( i, nDataType, pData, 0, dTotal, 0, PI2 );

		ezd_line( x_hDib, x, y,
						  x + (int)( (double)rad * cos( pos + v ) ),
						  y + (int)( (double)rad * sin( pos + v ) ),
						  *pCols );

		ezd_flood_fill( x_hDib, x + (int)( (double)rad / (double)2 * cos( pos + v / 2 ) ),
								y + (int)( (double)rad / (double)2 * sin( pos + v / 2 ) ),
								*pCols, pCols[ c ] );

		pos += v;

	} // end for

	return 1;
}

typedef struct _SAsciiData
{
	int sw;
	unsigned char *buf;
} SAsciiData;

int ascii_writer( void *pUser, int x, int y, int c, int f )
{
	SAsciiData *p = (SAsciiData*)pUser;
	unsigned char ch = (unsigned char)( f & 0xff );

	if ( !p )
		return 0;

	if ( ( '0' <= ch && '9' >= ch )
		 || ( 'A' <= ch && 'Z' >= ch )
		 || ( 'a' <= ch && 'z' >= ch ) )
		
		// Write the character
		p->buf[ y * p->sw + x ] = (unsigned char)f;

	else
		
		// Write the color
		p->buf[ y * p->sw + x ] = (unsigned char)c;
	
	return 1;
}

typedef struct _SDotMatrixData
{
	int w;
	int h;
	HEZDIMAGE pDib;
} SDotMatrixData;

int dotmatrix_writer( void *pUser, int x, int y, int c, int f )
{
	int cc, r, dw = 3;
	HEZDIMAGE hDib = (HEZDIMAGE)pUser;

	if ( !hDib )
		return 0;

	cc = c & 0xff;
	for ( r = 0; r < dw; r++ )
	{	ezd_circle( hDib, x * dw * 2 , y * dw * 2, r, cc );
		if ( r ) cc >>= 1;
	} // end for

	cc = ( c >> 8 ) & 0xff;
	for ( r = 0; r < dw; r++ )
	{	ezd_circle( hDib, x * dw * 2 + dw, y * dw * 2, r, cc << 8 );
		if ( r ) cc >>= 1;
	} // end for
		
	cc = c & 0xff;
	for ( r = 0; r < dw; r++ )
	{	ezd_circle( hDib, x * dw * 2 + dw, y * dw * 2 + dw, r, cc );
		if ( r ) cc >>= 1;
	} // end for

	cc = ( c >> 16 ) & 0xff;	
	for ( r = 0; r < dw; r++ )
	{	ezd_circle( hDib, x * dw * 2, y * dw * 2 + dw, r, cc << 16 );
		if ( r ) cc >>= 1;
	} // end for

	return 1;
}

int main( int argc, char* argv[] )
{
	int b, x, y;
	HEZDIMAGE hDib;
	HEZDFONT hFont;

	// Create output file name

	// Create image
	hDib = ezd_create( 640, -480, 32, 0 );
	if ( !hDib )
		return 1 ;

	// Fill in the background
	ezd_fill( hDib, 0x404040 );

	// Test fonts
	hFont = ezd_load_font( EZD_FONT_TYPE_MEDIUM, 0, 0 );
	if ( hFont )
		ezd_text( hDib, hFont, "--- EZDIB Test ---", -1, 10, 10, 0xffffff );

	// Draw random lines
	for ( x = 20; x < 300; x += 10 )
		ezd_line( hDib, x, ( x & 1 ) ? 50 : 100, x + 10, !( x & 1 ) ? 50 : 100, 0x00ff00 ),
			ezd_line( hDib, x + 10, ( x & 1 ) ? 50 : 100, x, !( x & 1 ) ? 50 : 100, 0x0000ff );

	// Random red box
	ezd_fill_rect( hDib, 200, 150, 400, 250, 0x900000 );

	// Random yellow box
	ezd_fill_rect( hDib, 300, 200, 350, 280, 0xffff00 );

	// Dark outline for yellow box
	ezd_rect( hDib, 300, 200, 350, 280, 0x000000 );

	// Draw random dots
	for ( y = 150; y < 250; y += 4 )
		for ( x = 50; x < 150; x += 4 )
			ezd_set_pixel( hDib, x, y, 0xffffff );

	// Circles
	for ( x = 0; x < 40; x++ )
		ezd_circle( hDib, 400, 60, x, x * 5 );

	// Draw graphs
	{
		// Graph data
		int data[] = { 11, 54, 23, 87, 34, 54, 75, 44, 66 };

		// Graph colors
		int cols[] = { 0xffffff, 0x400000, 0x006000, 0x000080 };

		// Draw bar graph
		ezd_rect( hDib, 35, 295, 605, 445, cols[ 0 ] );
		bar_graph( hDib, hFont, 40, 300, 600, 440, EZD_TYPE_INT,
				data, sizeof( data ) / sizeof( data[ 0 ] ),
				cols, sizeof( cols ) / sizeof( cols[ 0 ] ) );

		// Draw pie graph
		ezd_circle( hDib, 525, 150, 84, cols[ 0 ] );
		pie_graph( hDib, 525, 150, 80, EZD_TYPE_INT,
				data, sizeof( data ) / sizeof( data[ 0 ] ),
				cols, sizeof( cols ) / sizeof( cols[ 0 ] ) );

	}

	// Save the test image
	ezd_save( hDib, "output.bmp");

	/// Releases the specified font
	if ( hFont )
		ezd_destroy_font( hFont );

	// Free resources
	if ( hDib )
		ezd_destroy( hDib );

	return 0;
}
