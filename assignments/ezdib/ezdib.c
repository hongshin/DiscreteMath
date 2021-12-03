/*------------------------------------------------------------------
// Copyright (c) 1997 - 2012
// Robert Umbehant
// ezdib@wheresjames.com
// http://www.wheresjames.com
//
// Redistribution and use in source and binary forms, with or
// without modification, are permitted for commercial and
// non-commercial purposes, provided that the following
// conditions are met:
//
// * Redistributions of source code must retain the above copyright
//   notice, this list of conditions and the following disclaimer.
// * The names of the developers or contributors may not be used to
//   endorse or promote products derived from this software without
//   specific prior written permission.
//
//   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
//   CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
//   INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
//   MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
//   DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
//   CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
//   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
//   NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
//   LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
//   HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
//   CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
//   OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
//   EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//----------------------------------------------------------------*/

#include "ezdib.h"

//------------------------------------------------------------------
// Config
//------------------------------------------------------------------

/// Enable static fonts
/**
	This will prevent the creation of a font index, so font drawing 
	will be slightly slower.  Unless you are on a memory constrained 
	system, you will probably prefer to leave this on.
*/
// #define EZD_STATIC_FONTS

/// Define if you do not have string.h
// #define EZD_NO_MEMCPY

/// Define if you do not have malloc, calloc, and free, 
/**
	ezd_flood_file() will not work.
*/
// #define EZD_NO_ALLOCATION

/// If you have no file handling routines
/**
	ezd_save() will not work
*/
// #define EZD_NO_FILES

/// If you do not have math.h.  Sorry, you won't get circles
/**
	ezd_circle() and ezd_arc() will not work
*/
// #define EZD_NO_MATH

// Debugging
#if defined( _DEBUG )
#	define EZD_DEBUG
#endif

//------------------------------------------------------------------
// Internal config
//------------------------------------------------------------------

#if !defined( EZD_NO_FILES )
#	include <stdio.h>
#endif

// malloc, calloc, free
#if !defined( EZD_NO_ALLOCATION )
#	if !defined( EZD_NO_STDLIB )
#		include <stdlib.h>
#	else
		// No debug functions without stdlib
#		undef EZD_DEBUG
#	endif
#	if !defined( EZD_malloc )
#		define EZD_malloc malloc
#	endif
#	if !defined( EZD_calloc )
#		define EZD_calloc calloc
#	endif
#	if !defined( EZD_free )
#		define EZD_free free
#	endif
#else
	// Must use static fonts if no allocation routines
#	define EZD_STATIC_FONTS
	// Assume our debug functions won't work either
#	undef EZD_DEBUG
#endif

// sin(), cos()
#if !defined( EZD_NO_MATH )
#	include <math.h>
#endif

// memcpy() and memset() substitutes
#if defined( EZD_NO_MEMCPY )
#	define EZD_MEMCPY ezd_memcpy
#	define EZD_MEMSET ezd_memset
static void ezd_memcpy( char *pDst, const char *pSrc, int sz )
{	while ( 0 < sz-- )
		*(char*)pDst++ = *(char*)pSrc++;
}
static void ezd_memset( char *pDst, int v, int sz )
{	while ( 0 < sz-- )
		*(char*)pDst++ = (char)v;
}
#else
#	include <string.h>
#	define EZD_MEMCPY memcpy
#	define EZD_MEMSET memset
#endif

#if defined( EZD_DEBUG )
#	define _MSG( m ) printf( "\n%s(%d): %s() : %s\n", __FILE__, __LINE__, __FUNCTION__, m )
#	define _SHOW( f, ... ) printf( "\n%s(%d): %s() : " f "\n", __FILE__, __LINE__, __FUNCTION__, __VA_ARGS__ )
#	define _ERR( r, m ) ( _MSG( m ), r )
#else
#	define _MSG( m )
#	define _SHOW( ... )
#	define _ERR( r, m ) ( r )
#endif

//------------------------------------------------------------------
// Data structures
//------------------------------------------------------------------

#if !defined( EZD_NOPACK )
#	pragma pack( push, 1 )
#endif

/// DIB file magic number
#define EZD_MAGIC_NUMBER	0x4d42

/// Header for a standard dib file (.bmp)
typedef struct _SDIBFileHeader
{
	/// Magic number, must be 0x42 0x4D (BM)
	unsigned short	uMagicNumber;

	/// Size of the file in bytes
	unsigned int	uSize;

	/// Reserved
	unsigned short	uReserved1;

	/// Reserved
	unsigned short	uReserved2;

	/// Offset to start of image data
	unsigned int	uOffset;

} SDIBFileHeader;

/// Standard bitmap structure
typedef struct _SBitmapInfoHeader
{
	/// Size of this structure
	unsigned int			biSize;

	/// Image width
	int						biWidth;

	/// Image height
	int						biHeight;

	/// Number of bit planes in the image
	unsigned short			biPlanes;

	/// Bits per pixel / color depth
	unsigned short			biBitCount;

	/// Type of compression used
	unsigned int			biCompression;

	/// The total size of the image data
	unsigned int			biSizeImage;

	/// Horizontal resolution in pixels per meter
	int						biXPelsPerMeter;

	/// Vertical resolution in pixels per meter
	int						biYPelsPerMeter;

	/// Total number of colors actually used in the image,
	/// zero for all colors used.
	unsigned int			biClrUsed;

	/// Number of colors required for displaying the image,
	/// zero for all colors required.
	unsigned int			biClrImportant;

} SBitmapInfoHeader;

#	define EZD_FLAG_FREE_BUFFER		0x00010000

// Returns non-zero if any color components are greater than the threshold
#	define EZD_COMPARE_THRESHOLD( c, t ) ( ( c & 0xff ) > t \
										 || ( ( c >> 8 ) & 0xff ) > t \
										 || ( ( c >> 16 ) & 0xff ) > t )
										 
// This structure contains the memory image
typedef struct _SImageData
{
	/// Windows compatible image information
	SBitmapInfoHeader		bih;

	/// Color palette for 1 bit images
	int						colPalette[ 2 ];

	/// Threshold color for 1 bit images
	int						colThreshold;

	/// Image flags
	unsigned int			uFlags;
	
	/// User set pixel callback function
	t_ezd_set_pixel			pfSetPixel;
	
	/// User data passed to set pixel callback function
	void					*pSetPixelUser;

	/// User image pointer
	unsigned char			*pImage;

	/// Image data
	unsigned char			pBuffer[ 4 ];

} SImageData;

#if !defined( EZD_STATIC_FONTS )

// This structure contains the memory image
typedef struct _SFontData
{
	/// Font flags
	unsigned int			uFlags;

	/// Font index pointers
	const unsigned char		*pIndex[ 256 ];

	/// Font bitmap data
	unsigned char			pGlyph[ 1 ];

} SFontData;

#endif

#if !defined( EZD_NOPACK )
#	pragma pack( pop )
#endif

void ezd_destroy( HEZDIMAGE x_hDib )
{
#if !defined( EZD_NO_ALLOCATION )
	if ( x_hDib )
	{	SImageData *p = (SImageData*)x_hDib;
		if ( EZD_FLAG_FREE_BUFFER & p->uFlags )
			EZD_free( (SImageData*)x_hDib );
	} // end if
#endif
}

int ezd_header_size()
{
	return sizeof( SImageData );
}

HEZDIMAGE ezd_initialize( void *x_pBuffer, int x_nBuffer, int x_lWidth, int x_lHeight, int x_lBpp, unsigned int x_uFlags )
{
	int nImageSize;
	SImageData *p;

	// Ensure the user buffer is acceptable
	if ( !x_pBuffer || ( 0 < x_nBuffer && sizeof( SImageData ) > x_nBuffer ) )
		return _ERR( (HEZDIMAGE)0, "Invalid header buffer" );

	// Sanity check
	if ( !x_lWidth || !x_lHeight )
		return _ERR( (HEZDIMAGE)0, "Invalid parameters" );

	// Calculate image size
	nImageSize = EZD_IMAGE_SIZE( x_lWidth, x_lHeight, x_lBpp, 4 );
	if ( 0 >= nImageSize )
		return _ERR( (HEZDIMAGE)0, "Invalid bits per pixel" );

	// Point to users buffer
	p = (SImageData*)x_pBuffer;
		
	// Initialize the memory
	EZD_MEMSET( (char*)p, 0, sizeof( SImageData ) );

	// Initialize image metrics
	p->bih.biSize = sizeof( SBitmapInfoHeader );
	p->bih.biWidth = x_lWidth;
	p->bih.biHeight = x_lHeight;
	p->bih.biPlanes = 1;
	p->bih.biBitCount = x_lBpp;
	p->bih.biSizeImage = nImageSize;
	
	// Initialize color palette
	if ( 1 == x_lBpp )
	{	p->bih.biClrUsed = 2;
		p->bih.biClrImportant = 2;
		p->colPalette[ 0 ] = 0;
		p->colPalette[ 1 ] = 0xffffff;
	} // end if
	
	// Point image buffer
	p->pImage = ( EZD_FLAG_USER_IMAGE_BUFFER & x_uFlags ) ? 0 : p->pBuffer;
	
	// Save the flags
	p->uFlags = x_uFlags;

	return (HEZDIMAGE)p;
}


HEZDIMAGE ezd_create( int x_lWidth, int x_lHeight, int x_lBpp, unsigned int x_uFlags )
{
#if defined( EZD_NO_ALLOCATION )
	return 0;
#else
	int nImageSize;
	SImageData *p;

	// Make sure the caller isn't stepping on our internal flags
	if ( 0xffff0000 & x_uFlags )
		return _ERR( (HEZDIMAGE)0, "You have specified invalid flags" );
	
	// Sanity check
	if ( !x_lWidth || !x_lHeight )
		return _ERR( (HEZDIMAGE)0, "Invalid image width or height" );

	// Calculate image size
	nImageSize = EZD_IMAGE_SIZE( x_lWidth, x_lHeight, x_lBpp, 4 );
	if ( 0 >= nImageSize )
		return _ERR( (HEZDIMAGE)0, "Invalid bits per pixel" );
		
	// Allocate memory
	p = (SImageData*)EZD_malloc( sizeof( SImageData )
								 + ( ( EZD_FLAG_USER_IMAGE_BUFFER & x_uFlags ) ? 0 : nImageSize ) );

	if ( !p )
		return 0;

	// Initialize the header
	return ezd_initialize( p, sizeof( SImageData ), x_lWidth, x_lHeight, x_lBpp, x_uFlags | EZD_FLAG_FREE_BUFFER );
#endif
}

int ezd_set_image_buffer( HEZDIMAGE x_hDib, void *x_pImg, int x_nImg )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
	{	_MSG( "Invalid parameters" ); return 0; }

	// Verify image buffer size if needed
	if ( x_pImg && 0 < x_nImg && x_nImg < (int)p->bih.biSizeImage )
	{	_MSG( "Invalid user image buffer size" ); return 0; }

	// Save user image pointer
	p->pImage = ( !x_pImg && !( EZD_FLAG_USER_IMAGE_BUFFER & p->uFlags ) ) 
				? p->pBuffer : x_pImg;
	return 1;
}

int ezd_set_pixel_callback( HEZDIMAGE x_hDib, t_ezd_set_pixel x_pf, void *x_pUser )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( 0, "Invalid parameters" );
	
	// Save user callback info
	p->pfSetPixel = x_pf;
	p->pSetPixelUser = x_pUser;
	
	return 1;
}


int ezd_set_palette_color( HEZDIMAGE x_hDib, int x_idx, int x_col )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( 0, "Invalid parameters" );

	if ( 0 > x_idx || 1 < x_idx )
		return _ERR( 0, "Palette index out of range" );

	// Set this palette color
	p->colPalette[ x_idx ] = x_col;
	
	return 1;
}

int ezd_get_palette_color( HEZDIMAGE x_hDib, int x_idx, int x_col )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( 0, "Invalid parameters" );

	if ( 0 > x_idx || 1 < x_idx )
		return _ERR( 0, "Palette index out of range" );

	// Return this palette color
	return p->colPalette[ x_idx ];
}

int* ezd_get_palette( HEZDIMAGE x_hDib )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( (int*)0, "Invalid parameters" );

	// Return a pointer to the palette
	return p->colPalette;
}

int ezd_get_palette_size( HEZDIMAGE x_hDib )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( 0, "Invalid parameters" );

	switch( p->bih.biBitCount )
	{
		case 1 :
			return 2;
	} // end switch

	return 0;
}

int ezd_set_color_threshold( HEZDIMAGE x_hDib, int x_col )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( 0, "Invalid parameters" );

	// Calculate scan width
	p->colThreshold = x_col;
	
	return 1;
}

int ezd_get_width( HEZDIMAGE x_hDib )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( 0, "Invalid parameters" );

	// Calculate scan width
	return p->bih.biWidth;
}

int ezd_get_height( HEZDIMAGE x_hDib )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( 0, "Invalid parameters" );

	// Calculate scan width
	return p->bih.biHeight;
}

int ezd_get_bpp( HEZDIMAGE x_hDib )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( 0, "Invalid parameters" );

	// Calculate scan width
	return p->bih.biBitCount;
}

int ezd_get_image_size( HEZDIMAGE x_hDib )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( 0, "Invalid parameters" );

	// Calculate scan width
	return p->bih.biSizeImage;
}


void* ezd_get_image_ptr( HEZDIMAGE x_hDib )
{
	SImageData *p = (SImageData*)x_hDib;
	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize )
		return _ERR( (void*)0, "Invalid parameters" );

	// Calculate scan width
	return p->pImage;
}


int ezd_save( HEZDIMAGE x_hDib, const char *x_pFile )
{
#if defined( EZD_NO_FILES )
	return 0;
#else
	FILE *fh;
	int palette_size = 0;
	SDIBFileHeader dfh;
	SImageData *p = (SImageData*)x_hDib;

	// Sanity checks
	if ( !x_pFile || !*x_pFile || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize || !p->pImage )
		return _ERR( 0, "Invalid parameters" );

	// Ensure packing is ok
	if ( sizeof( SDIBFileHeader ) != 14 )
		return _ERR( 0, "Structure packing for DIB header is incorrect" );

	// Ensure packing is ok
	if ( sizeof( SBitmapInfoHeader ) != 40 )
		return _ERR( 0, "Structure packing for BITMAP header is incorrect" );

	// Add palettte size
	if ( 1 == p->bih.biBitCount )
		palette_size = sizeof( p->colPalette[ 0 ] ) * 2;
		
	// Attempt to open the output file
	fh = fopen ( x_pFile, "wb" );
	if ( !fh )
		return _ERR( 0, "Failed to open DIB file for writing" );

	// Fill in header info
	dfh.uMagicNumber = EZD_MAGIC_NUMBER;
	dfh.uSize = sizeof( SDIBFileHeader ) + p->bih.biSize + p->bih.biSizeImage;
	dfh.uReserved1 = 0;
	dfh.uReserved2 = 0;
	dfh.uOffset = sizeof( SDIBFileHeader ) + p->bih.biSize + palette_size;

	// Write the header
	if ( sizeof( dfh ) != fwrite( &dfh, 1, sizeof( dfh ), fh ) )
	{	fclose( fh ); return _ERR( 0, "Error writing DIB header" ); }

	// Write the Bitmap header
	if ( p->bih.biSize != fwrite( &p->bih, 1, p->bih.biSize, fh ) )
	{	fclose( fh ); return _ERR( 0, "Error writing bitmap header" ); }

	// Write the color palette if needed
	if ( 0 < palette_size )
		if ( sizeof( p->colPalette ) != fwrite( p->colPalette, 1, palette_size, fh ) )
		{	fclose( fh ); return _ERR( 0, "Error writing palette" ); }

	// Write the Image data
	if ( p->bih.biSizeImage != fwrite( p->pImage, 1, p->bih.biSizeImage, fh ) )
	{	fclose( fh ); return _ERR( 0, "Error writing image data" ); }

	// Close the file handle
	fclose( fh );

	return 1;
#endif
}

int ezd_fill( HEZDIMAGE x_hDib, int x_col )
{
	int w, h, sw, pw, x, y;
	SImageData *p = (SImageData*)x_hDib;

	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize 
		 || ( !p->pImage && !p->pfSetPixel ) )
		return _ERR( 0, "Invalid parameters" );
		
	// Calculate image metrics
	w = EZD_ABS( p->bih.biWidth );
	h = EZD_ABS( p->bih.biHeight );

	// Check for user callback function
	if ( p->pfSetPixel )
	{
		// Fill each pixel
		for ( y = 0; y < h; y++ )
			for( x = 0; x < w; x++ )
				if ( !p->pfSetPixel( p->pSetPixelUser, x, y, x_col, 0 ) )
					return 0;
				
		return 1;

	} // end if

	// Pixel and scan widths
	pw = EZD_FITTO( p->bih.biBitCount, 8 );
	sw = EZD_SCANWIDTH( w, p->bih.biBitCount, 4 );

	// Set the first line
	switch( p->bih.biBitCount )
	{
		case 1 :
			EZD_MEMSET( p->pImage, EZD_COMPARE_THRESHOLD( x_col, p->colThreshold ) ? 0xff : 0, sw );
			break;
			
		case 24 :
		{
			// Color values
			unsigned char r = x_col & 0xff;
			unsigned char g = ( x_col >> 8 ) & 0xff;
			unsigned char b = ( x_col >> 16 ) & 0xff;
			unsigned char *pImg = p->pImage;

			// Set the first line
			for( x = 0; x < w; x++, pImg += pw )
				pImg[ 0 ] = r, pImg[ 1 ] = g, pImg[ 2 ] = b;

		} break;

		case 32 :
		{
			// Set the first line
			int *pImg = (int*)p->pImage;
			for( x = 0; x < w; x++, pImg++ )
				*pImg = x_col;

		} break;

		default :
			return 0;

	} // end switch

	// Copy remaining lines
	for( y = 1; y < h; y++ )
		EZD_MEMCPY( &p->pImage[ y * sw ], p->pImage, sw );

	return 1;
}

int ezd_set_pixel( HEZDIMAGE x_hDib, int x, int y, int x_col )
{
	int w, h, sw, pw;
	SImageData *p = (SImageData*)x_hDib;

	if ( !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize
		 || ( !p->pImage && !p->pfSetPixel ) )
		return _ERR( 0, "Invalid parameters" );

	// Calculate image metrics
	w = EZD_ABS( p->bih.biWidth );
	h = EZD_ABS( p->bih.biHeight );

	// Ensure pixel is within the image
	if ( 0 > x || x >= w || 0 > y || y >= h )
	{	_SHOW( "Point out of range : %d,%d : %dx%d ", x, y, w, h );
		return 0;
	} // en dif

	// Set the specified pixel
	if ( p->pfSetPixel )
		return p->pfSetPixel( p->pSetPixelUser, x, y, x_col, 0 );

	// Pixel and scan width
	pw = EZD_FITTO( p->bih.biBitCount, 8 );
	sw = EZD_SCANWIDTH( w, p->bih.biBitCount, 4 );

	// Set the first line
	switch( p->bih.biBitCount )
	{
		case 1 :
			p->pImage[ y * sw + ( x >> 3 ) ] |= 0x80 >> ( x & 7 );
			break;

		case 24 :
		{
			// Color values
			unsigned char r = x_col & 0xff;
			unsigned char g = ( x_col >> 8 ) & 0xff;
			unsigned char b = ( x_col >> 16 ) & 0xff;
			unsigned char *pImg = &p->pImage[ y * sw + x * pw ];

			// Set the pixel color
			pImg[ 0 ] = r, pImg[ 1 ] = g, pImg[ 2 ] = b;

		} break;

		case 32 :
			*(unsigned int*)&p->pImage[ y * sw + x * pw ] = x_col;
			break;

		default :
			return 0;

	} // end switch

	return 1;
}

int ezd_get_pixel( HEZDIMAGE x_hDib, int x, int y )
{
	int w, h, sw, pw;
	SImageData *p = (SImageData*)x_hDib;

	if ( !p || !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize || !p->pImage )
		return _ERR( 0, "Invalid parameters" );

	// Calculate image metrics
	w = EZD_ABS( p->bih.biWidth );
	h = EZD_ABS( p->bih.biHeight );

	// Ensure pixel is within the image
	if ( 0 > x || x >= w || 0 > y || y >= h )
	{	_SHOW( "Point out of range : %d,%d : %dx%d ", x, y, w, h );
		return 0;
	} // en dif

	// Pixel and scan width
	pw = EZD_FITTO( p->bih.biBitCount, 8 );
	sw = EZD_SCANWIDTH( w, p->bih.biBitCount, 4 );

	// Set the first line
	switch( p->bih.biBitCount )
	{
		case 1 :
			return p->colPalette[ ( p->pImage[ y * sw + ( x >> 3 ) ] & ( 0x80 >> ( x & 7 ) ) ) ? 1 : 0 ];

		case 24 :
		{
			// Return the color of the specified pixel
			unsigned char *pImg = &p->pImage[ y * sw + x * pw ];
			return pImg[ 0 ] | ( pImg[ 1 ] << 8 ) | ( pImg[ 2 ] << 16 );

		} break;

		case 32 :
			return *(unsigned int*)&p->pImage[ y * sw + x * pw ];

	} // end switch

	return 0;
}

int ezd_line( HEZDIMAGE x_hDib, int x1, int y1, int x2, int y2, int x_col )
{
	int w, h, sw, pw, xd, yd, xl, yl, done = 0;
	SImageData *p = (SImageData*)x_hDib;

	if ( !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize
		 || ( !p->pImage && !p->pfSetPixel ) )
		return _ERR( 0, "Invalid parameters" );

	// Calculate image metrics
	w = EZD_ABS( p->bih.biWidth );
	h = EZD_ABS( p->bih.biHeight );

	// Determine direction and distance
	xd = ( x1 < x2 ) ? 1 : -1;
	yd = ( y1 < y2 ) ? 1 : -1;
	xl = ( x1 < x2 ) ? ( x2 - x1 ) : ( x1 - x2 );
	yl = ( y1 < y2 ) ? ( y2 - y1 ) : ( y1 - y2 );

	// Check for user callback function
	if ( p->pfSetPixel )
	{
		int mx = 0, my = 0, c = EZD_COMPARE_THRESHOLD( x_col, p->colThreshold );
		static unsigned char xm[] = { 0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01 };

		// Draw the line
		while ( !done )
		{
			if ( x1 == x2 && y1 == y2 )
				done = 1;

			// Plot pixel
			if ( 0 <= x1 && x1 < w && 0 <= y1 && y1 < h )
				if ( !p->pfSetPixel( p->pSetPixelUser, x1, y1, x_col, 0 ) )
					return 0;

			mx += xl;
			if ( x1 != x2 && mx > yl )
				x1 += xd, mx -= yl;

			my += yl;
			if ( y1 != y2 && my > xl )
				y1 += yd, my -= xl;

		} // end while
				
		return 1;

	} // end if

	// Pixel and scan width
	pw = EZD_FITTO( p->bih.biBitCount, 8 );
	sw = EZD_SCANWIDTH( w, p->bih.biBitCount, 4 );

	// Set the first line
	switch( p->bih.biBitCount )
	{
		case 1 :
		{
			int mx = 0, my = 0, c = EZD_COMPARE_THRESHOLD( x_col, p->colThreshold );
			static unsigned char xm[] = { 0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01 };

			// Draw the line
			while ( !done )
			{
				if ( x1 == x2 && y1 == y2 )
					done = 1;

				// Plot pixel
				if ( 0 <= x1 && x1 < w && 0 <= y1 && y1 < h )
					if ( c )
						p->pImage[ y1 * sw + ( x1 >> 3 ) ] |= xm[ x1 & 7 ];
					else
						p->pImage[ y1 * sw + ( x1 >> 3 ) ] &= ~xm[ x1 & 7 ];

				mx += xl;
				if ( x1 != x2 && mx > yl )
					x1 += xd, mx -= yl;

				my += yl;
				if ( y1 != y2 && my > xl )
					y1 += yd, my -= xl;

			} // end while

		} break;
	
		case 24 :
		{
			// Color values
			unsigned char r = x_col & 0xff;
			unsigned char g = ( x_col >> 8 ) & 0xff;
			unsigned char b = ( x_col >> 16 ) & 0xff;
			unsigned char *pImg;
			int mx = 0, my = 0;

			while ( !done )
			{
				if ( x1 == x2 && y1 == y2 )
					done = 1;

				// Plot pixel
				if ( 0 <= x1 && x1 < w && 0 <= y1 && y1 < h )
				{	pImg = &p->pImage[ y1 * sw + x1 * pw ];
					pImg[ 0 ] = r, pImg[ 1 ] = g, pImg[ 2 ] = b;
				} // end if

				mx += xl;
				if ( x1 != x2 && mx > yl )
					x1 += xd, mx -= yl;

				my += yl;
				if ( y1 != y2 && my > xl )
					y1 += yd, my -= xl;

			} // end while

		} break;

		case 32 :
		{
			// Color values
			int mx = 0, my = 0;

			// Draw the line
			while ( !done )
			{
				if ( x1 == x2 && y1 == y2 )
					done = 1;

				// Plot pixel
				if ( 0 <= x1 && x1 < w && 0 <= y1 && y1 < h )
					*(unsigned int*)&p->pImage[ y1 * sw + x1 * pw ] = x_col;

				mx += xl;
				if ( x1 != x2 && mx > yl )
					x1 += xd, mx -= yl;

				my += yl;
				if ( y1 != y2 && my > xl )
					y1 += yd, my -= xl;

			} // end while

		} break;

		default :
			return 0;

	} // end switch

	return 1;
}

int ezd_rect( HEZDIMAGE x_hDib, int x1, int y1, int x2, int y2, int x_col )
{
	// Draw rectangle
	return 		ezd_line( x_hDib, x1, y1, x2, y1, x_col )
		   && 	ezd_line( x_hDib, x2, y1, x2, y2, x_col )
		   &&	ezd_line( x_hDib, x2, y2, x1, y2, x_col )
		   &&	ezd_line( x_hDib, x1, y2, x1, y1, x_col );
}

#define EZD_PI		( (double)3.141592654 )
#define EZD_PI2		( EZD_PI * (double)2 )
#define EZD_PI4		( EZD_PI * (double)4 )

int ezd_arc( HEZDIMAGE x_hDib, int x, int y, int x_rad, double x_dStart, double x_dEnd, int x_col )
{
#if defined( EZD_NO_MATH )
	return 0;
#else
	double arc;
	int i, w, h, sw, pw, px, py;
	int res = (int)( (double)x_rad * EZD_PI4 ), resdraw;
	unsigned char *pImg;
	SImageData *p = (SImageData*)x_hDib;

	if ( !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize
		 || ( !p->pImage && !p->pfSetPixel ) )
		return _ERR( 0, "Invalid parameters" );

	// Dont' draw null arc
	if ( x_dStart == x_dEnd )
		return 1;

	// Ensure correct order
	else if ( x_dStart > x_dEnd )
	{	double t = x_dStart;
		x_dStart = x_dEnd;
		x_dEnd = t;
	} // end if

	// Get arc size
	arc = x_dEnd - x_dStart;

	// How many points to draw
	resdraw = ( EZD_PI2 <= arc ) ? res : (int)( arc * (double)res / EZD_PI2 );

	// Calculate image metrics
	w = EZD_ABS( p->bih.biWidth );
	h = EZD_ABS( p->bih.biHeight );

	// Ensure pixel is within the image
	if ( 0 > x || x >= w || 0 > y || y >= h )
	{	_SHOW( "Point out of range : %d,%d : %dx%d ", x, y, w, h );
		return 0;
	} // en dif

	// Check for user callback function
	if ( p->pfSetPixel )
	{
		// Draw the circle
		for ( i = 0; i < resdraw; i++ )
		{
			// Offset for this pixel
			px = x + (int)( (double)x_rad * cos( x_dStart + (double)i * EZD_PI2 / (double)res ) );
			py = y + (int)( (double)x_rad * sin( x_dStart + (double)i * EZD_PI2 / (double)res ) );

			// Plot pixel
			if ( 0 <= px && px < w && 0 <= py && py < h )
				if ( !p->pfSetPixel( p->pSetPixelUser, px, py, x_col, 0 ) )
					return 0;
					
		} // end while
	
		return 1;

	} // end if

	// Pixel and scan width
	pw = EZD_FITTO( p->bih.biBitCount, 8 );
	sw = EZD_SCANWIDTH( w, p->bih.biBitCount, 4 );

	switch( p->bih.biBitCount )
	{
		case 1:
		{
			int c = EZD_COMPARE_THRESHOLD( x_col, p->colThreshold );
			static unsigned char xm[] = { 0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01 };

			// Draw the circle
			for ( i = 0; i < resdraw; i++ )
			{
				// Offset for this pixel
				px = x + (int)( (double)x_rad * cos( x_dStart + (double)i * EZD_PI2 / (double)res ) );
				py = y + (int)( (double)x_rad * sin( x_dStart + (double)i * EZD_PI2 / (double)res ) );

				// Plot pixel
				if ( 0 <= px && px < w && 0 <= py && py < h )
					if ( c )
						p->pImage[ py * sw + ( px >> 3 ) ] |= xm[ px & 7 ];
					else
						p->pImage[ py * sw + ( px >> 3 ) ] &= ~xm[ px & 7 ];
						
			} // end while

		} break;

		case 24 :
		{
			// Color values
			unsigned char r = x_col & 0xff;
			unsigned char g = ( x_col >> 8 ) & 0xff;
			unsigned char b = ( x_col >> 16 ) & 0xff;
			for ( i = 0; i < resdraw; i++ )
			{
				// Offset for this pixel
				px = x + (int)( (double)x_rad * cos( x_dStart + (double)i * EZD_PI2 / (double)res ) );
				py = y + (int)( (double)x_rad * sin( x_dStart + (double)i * EZD_PI2 / (double)res ) );

				// If it falls on the image
				if ( 0 <= px && px < w && 0 <= py && py < h )
				{	pImg = &p->pImage[ py * sw + px * pw ];
					pImg[ 0 ] = r, pImg[ 1 ] = g, pImg[ 2 ] = b;
				} // end if

			} // end for

		} break;

		case 32 :
			for ( i = 0; i < resdraw; i++ )
			{
				// Offset for this pixel
				px = x + (int)( (double)x_rad * sin( (double)i * EZD_PI2 / (double)res ) );
				py = y + (int)( (double)x_rad * cos( (double)i * EZD_PI2 / (double)res ) );

				// If it falls on the image
				if ( 0 <= px && px < w && 0 <= py && py < h )
					*(unsigned int*)&p->pImage[ py * sw + px * pw ] = x_col;

			} // end for

			break;

		default :
			return 0;

	} // end switch

	return 1;
#endif
}


int ezd_circle( HEZDIMAGE x_hDib, int x, int y, int x_rad, int x_col )
{
	return ezd_arc( x_hDib, x, y, x_rad, 0, EZD_PI2, x_col );
}

int ezd_fill_rect( HEZDIMAGE x_hDib, int x1, int y1, int x2, int y2, int x_col )
{
	int w, h, x, y, sw, pw, fw, fh;
	unsigned char *pStart, *pPos;
	SImageData *p = (SImageData*)x_hDib;

	if ( !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize
		 || ( !p->pImage && !p->pfSetPixel ) )
		return _ERR( 0, "Invalid parameters" );

	// Calculate image metrics
	w = EZD_ABS( p->bih.biWidth );
	h = EZD_ABS( p->bih.biHeight );

	// Swap coords if needed
	if ( x1 > x2 ) { int t = x1; x1 = x2; x2 = t; }
	if ( y1 > y2 ) { int t = y1; y1 = y2; y2 = t; }

	// Clip
	if ( 0 > x1 ) x1 = 0; else if ( x1 >= w ) x1 = w - 1;
	if ( 0 > y1 ) y1 = 0; else if ( y1 >= h ) y1 = h - 1;
	if ( 0 > x2 ) x2 = 0; else if ( x2 >= w ) x2 = w - 1;
	if ( 0 > y2 ) y2 = 0; else if ( y2 >= h ) y2 = h - 1;

	// Fill width and height
	fw = x2 - x1;
	fh = y2 - y1;

	// Are we left with a valid region
	if ( 0 > fw || 0 > fh )
	{	_SHOW( "Invalid fill rect : %d,%d -> %d,%d : %dx%d ",
			   x1, y1, x2, y2, w, h );
		return 0;
	} // en dif

	// Check for user callback function
	if ( p->pfSetPixel )
	{
		// Fill each pixel
		for ( y = y1; y < y2; y++ )
			for( x = x1; x < x2; x++ )
				if ( 0 <= x && x < w && 0 <= y && y < h )
					if ( !p->pfSetPixel( p->pSetPixelUser, x, y, x_col, 0 ) )
						return 0;
				
		return 1;

	} // end if
	
	// Pixel and scan width
	pw = EZD_FITTO( p->bih.biBitCount, 8 );
	sw = EZD_SCANWIDTH( w, p->bih.biBitCount, 1 );

	// Set the first line
	switch( p->bih.biBitCount )
	{
		case 1 :
		{
			int c = EZD_COMPARE_THRESHOLD( x_col, p->colThreshold );
			static unsigned char xm[] = { 0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01 };

			// Just fill it in pixel by pixel for 1 bit images
			for ( y = y1; y < y2; y++ )
				for( x = x1; x < x2; x++ )
					if ( 0 <= x && x < w && 0 <= y && y < h )
						if ( c )
							p->pImage[ y * sw + ( x >> 3 ) ] |= xm[ x & 7 ];
						else
							p->pImage[ y * sw + ( x >> 3 ) ] &= ~xm[ x & 7 ];

			return 1;

		} break;

		case 24 :
		{
			// Color values
			unsigned char r = x_col & 0xff;
			unsigned char g = ( x_col >> 8 ) & 0xff;
			unsigned char b = ( x_col >> 16 ) & 0xff;
			pStart = pPos = &p->pImage[ y1 * sw + x1 * pw ];

			// Set the first line
			for( x = 0; x < fw; x++, pPos += pw )
				pPos[ 0 ] = r, pPos[ 1 ] = g, pPos[ 2 ] = b;

		} break;

		case 32 :
		{
			// Set the first line
			pStart = pPos = &p->pImage[ y1 * sw + x1 * pw ];
			for( x = 0; x < fw; x++, pPos += pw )
				*(unsigned int*)pPos = x_col;

		} break;

		default :
			return 0;

	} // end switch

	// Copy remaining lines
	pPos = pStart;
	for( y = 1; y < fh; y++ )
	{
		// Skip to next line
		pPos += sw;
		EZD_MEMCPY( pPos, pStart, fw * pw );

	} // end for

	return 1;
}

int ezd_flood_fill( HEZDIMAGE x_hDib, int x, int y, int x_bcol, int x_col )
{
#if defined( EZD_NO_ALLOCATION )
	return 0;
#else
	int ok, n, i, ii, w, h, sw, pw, bc;
	unsigned char r, g, b, br, bg, bb;
	unsigned char *pImg, *map;
	SImageData *p = (SImageData*)x_hDib;

	if ( !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize || !p->pImage )
		return _ERR( 0, "Invalid parameters" );

	// +++ Fix ezd_flood_fill() for 1 bpp
	if ( 1 == p->bih.biBitCount )
		return 0; // _ERR( 0, "Invalid pixel depth" );

	// Calculate image metrics
	w = EZD_ABS( p->bih.biWidth );
	h = EZD_ABS( p->bih.biHeight );

	// Ensure pixel is within the image
	if ( 0 > x || x >= w || 0 > y || y >= h )
	{	_SHOW( "Point out of range : %d,%d : %dx%d ", x, y, w, h );
		return 0;
	} // en dif

	// Pixel and scan width
	pw = EZD_FITTO( p->bih.biBitCount, 8 );
	sw = EZD_SCANWIDTH( w, p->bih.biBitCount, 4 );

	// Set the image pointer
	pImg = p->pImage;

	// Allocate space for fill map
	map = (unsigned char*)EZD_calloc( w * h, 1 );
	if ( !map )
		return 0;

	// Prepare 24 bit color components
	r = x_col & 0xff; g = ( x_col >> 8 ) & 0xff; b = ( x_col >> 16 ) & 0xff;
	br = x_bcol & 0xff; bg = ( x_bcol >> 8 ) & 0xff; bb = ( x_bcol >> 16 ) & 0xff;

	// Initialize indexes
	i = y * w + x;
	ii = y * sw + x * pw;

	// Save away bit count
	bc = p->bih.biBitCount;

	// Crawl the map
	while ( ( map[ i ] & 0x0f ) <= 3 )
	{
	
		if ( ( map[ i ] & 0x0f ) == 0 )
		{
			// In the name of simplicity
			switch( bc )
			{
				case 24 :
					pImg[ ii ] = r;
					pImg[ ii + 1 ] = g;
					pImg[ ii + 2 ] = b;
					break;

				case 32 :
					*(unsigned int*)&p->pImage[ ii ] = x_col;
					break;

			} // end switch

			// Point to next direction
			map[ i ] &= 0xf0, map[ i ] |= 1;

			// Can we go up?
			if ( y < ( h - 1 ) )
			{
				n = ( y + 1 ) * sw + x * pw;
				switch( bc )
				{	case 24 :
						ok = pImg[ n ] != r || pImg[ n + 1 ] != g || pImg[ n + 2 ] != b;
						if ( ok ) ok = pImg[ n ] != br || pImg[ n + 1 ] != bg || pImg[ n + 2 ] != bb;
						break;
					case 32 :
						ok = *(unsigned int*)&pImg[ n ] != x_col;
						if ( ok ) ok = *(unsigned int*)&pImg[ n ] != x_bcol;
						break;
				} // end switch

				if ( ok )
				{	y++;
					i = y * w + x;
					map[ i ] = 0x10;
					ii = n;
				} // end if

			} // end if

		} // end if

		if ( ( map[ i ] & 0x0f ) == 1 )
		{
			// Point to next direction
			map[ i ] &= 0xf0, map[ i ] |= 2;

			// Can we go right?
			if ( x < ( w - 1 ) )
			{
				n = y * sw + ( x + 1 ) * pw;
				switch( bc )
				{	case 24 :
						ok = pImg[ n ] != r || pImg[ n + 1 ] != g || pImg[ n + 2 ] != b;
						if ( ok ) ok = pImg[ n ] != br || pImg[ n + 1 ] != bg || pImg[ n + 2 ] != bb;
						break;
					case 32 :
						ok = *(unsigned int*)&pImg[ n ] != x_col;
						if ( ok ) ok = *(unsigned int*)&pImg[ n ] != x_bcol;
						break;
				} // end switch

				if ( ok )
				{	x++;
					i = y * w + x;
					map[ i ] = 0x20;
					ii = n;
				} // end if

			} // end if

		} // end if

		if ( ( map[ i ] & 0x0f ) == 2 )
		{
			// Point to next direction
			map[ i ] &= 0xf0, map[ i ] |= 3;

			// Can we go down?
			if ( y > 0 )
			{
				n = ( y - 1 ) * sw + x * pw;
				switch( bc )
				{	case 24 :
						ok = pImg[ n ] != r || pImg[ n + 1 ] != g || pImg[ n + 2 ] != b;
						if ( ok ) ok = pImg[ n ] != br || pImg[ n + 1 ] != bg || pImg[ n + 2 ] != bb;
						break;
					case 32 :
						ok = *(unsigned int*)&pImg[ n ] != x_col;
						if ( ok ) ok = *(unsigned int*)&pImg[ n ] != x_bcol;
						break;
				} // end switch

				if ( ok )
				{	y--;
					i = y * w + x;
					map[ i ] = 0x30;
					ii = n;
				} // end if

			} // end if

		} // end if

		if ( ( map[ i ] & 0x0f ) == 3 )
		{
			// Point to next
			map[ i ] &= 0xf0, map[ i ] |= 4;

			// Can we go left
			if ( x > 0 )
			{
				n = y * sw + ( x - 1 ) * pw;
				switch( bc )
				{	case 24 :
						ok = pImg[ n ] != r || pImg[ n + 1 ] != g || pImg[ n + 2 ] != b;
						if ( ok ) ok = pImg[ n ] != br || pImg[ n + 1 ] != bg || pImg[ n + 2 ] != bb;
						break;
					case 32 :
						ok = *(unsigned int*)&pImg[ n ] != x_col;
						if ( ok ) ok = *(unsigned int*)&pImg[ n ] != x_bcol;
						break;
				} // end switch

				if ( ok )
				{	x--;
					i = y * w + x;
					map[ i ] = 0x40;
					ii = n;
				} // end if

			} // end if

		} // end if

		// Time to backup?
		while ( ( map[ i ] & 0xf0 ) > 0 && ( map[ i ] & 0x0f ) > 3 )
		{
			// Go back
			if ( ( map[ i ] & 0xf0 ) == 0x10 ) y--;
			else if ( ( map[ i ] & 0xf0 ) == 0x20 ) x--;
			else if ( ( map[ i ] & 0xf0 ) == 0x30 ) y++;
			else if ( ( map[ i ] & 0xf0 ) == 0x40 ) x++;

			// Set indexes
			i = y * w + x;
			ii = y * sw + x * pw;

		} // end while

	} // end if

	EZD_free( map );

	return 1;
#endif
}

// A small font map
static const unsigned char font_map_small [] =
{
	// Default glyph
	'.', 1, 6,	0x08,

	// Tab width
	'\t', 8, 0,

	// Space
	' ', 3, 0,

	'!', 1, 6,	0xea,
	'+', 3, 6,	0x0b, 0xa0, 0x00,
	'-', 3, 6,	0x03, 0x80, 0x00,
	'/', 3, 6,	0x25, 0x48, 0x00,
	'*', 3, 6,	0xab, 0xaa, 0x00,
	'@', 4, 6,	0x69, 0xbb, 0x87,
	':', 1, 6,	0x52,
	'=', 3, 6,	0x1c, 0x70, 0x00,
	'?', 4, 6,	0x69, 0x24, 0x04,
	'%', 3, 6,	0x85, 0x28, 0x40,
	'^', 3, 6,	0x54, 0x00, 0x00,
	'#', 5, 6,	0x57, 0xd5, 0xf5, 0x00,
	'$', 5, 6,	0x23, 0xe8, 0xe2, 0xf8,
	'~', 4, 6,	0x05, 0xa0, 0x00,

	'0', 3, 6,	0x56, 0xd4, 0x31,
	'1', 2, 6,	0xd5, 0x42,
	'2', 4, 6,	0xe1, 0x68, 0xf0,
	'3', 4, 6,	0xe1, 0x61, 0xe0,
	'4', 4, 6,	0x89, 0xf1, 0x10,
	'5', 4, 6,	0xf8, 0xe1, 0xe0,
	'6', 4, 6,	0x78, 0xe9, 0x60,
	'7', 4, 6,	0xf1, 0x24, 0x40,
	'8', 4, 6,	0x69, 0x69, 0x60,
	'9', 4, 6,	0x69, 0x71, 0x60,

	'A', 4, 6,	0x69, 0xf9, 0x90,
	'B', 4, 6,	0xe9, 0xe9, 0xe0,
	'C', 4, 6,	0x78, 0x88, 0x70,
	'D', 4, 6,	0xe9, 0x99, 0xe0,
	'E', 4, 6,	0xf8, 0xe8, 0xf0,
	'F', 4, 6,	0xf8, 0xe8, 0x80,
	'G', 4, 6,	0x78, 0xb9, 0x70,
	'H', 4, 6,	0x99, 0xf9, 0x90,
	'I', 3, 6,	0xe9, 0x2e, 0x00,
	'J', 4, 6,	0xf2, 0x2a, 0x40,
	'K', 4, 6,	0x9a, 0xca, 0x90,
	'L', 3, 6,	0x92, 0x4e, 0x00,
	'M', 5, 6,	0x8e, 0xeb, 0x18, 0x80,
	'N', 4, 6,	0x9d, 0xb9, 0x90,
	'O', 4, 6,	0x69, 0x99, 0x60,
	'P', 4, 6,	0xe9, 0xe8, 0x80,
	'Q', 4, 6,	0x69, 0x9b, 0x70,
	'R', 4, 6,	0xe9, 0xea, 0x90,
	'S', 4, 6,	0x78, 0x61, 0xe0,
	'T', 3, 6,	0xe9, 0x24, 0x00,
	'U', 4, 6,	0x99, 0x99, 0x60,
	'V', 4, 6,	0x99, 0x96, 0x60,
	'W', 5, 6,	0x8c, 0x6b, 0x55, 0x00,
	'X', 4, 6,	0x99, 0x69, 0x90,
	'Y', 3, 6,	0xb5, 0x24, 0x00,
	'Z', 4, 6,	0xf2, 0x48, 0xf0,

	'a', 4, 6,	0x69, 0xf9, 0x90,
	'b', 4, 6,	0xe9, 0xe9, 0xe0,
	'c', 4, 6,	0x78, 0x88, 0x70,
	'd', 4, 6,	0xe9, 0x99, 0xe0,
	'e', 4, 6,	0xf8, 0xe8, 0xf0,
	'f', 4, 6,	0xf8, 0xe8, 0x80,
	'g', 4, 6,	0x78, 0xb9, 0x70,
	'h', 4, 6,	0x99, 0xf9, 0x90,
	'i', 3, 6,	0xe9, 0x2e, 0x00,
	'j', 4, 6,	0xf2, 0x2a, 0x40,
	'k', 4, 6,	0x9a, 0xca, 0x90,
	'l', 3, 6,	0x92, 0x4e, 0x00,
	'm', 5, 6,	0x8e, 0xeb, 0x18, 0x80,
	'n', 4, 6,	0x9d, 0xb9, 0x90,
	'o', 4, 6,	0x69, 0x99, 0x60,
	'p', 4, 6,	0xe9, 0xe8, 0x80,
	'q', 4, 6,	0x69, 0x9b, 0x70,
	'r', 4, 6,	0xe9, 0xea, 0x90,
	's', 4, 6,	0x78, 0x61, 0xe0,
	't', 3, 6,	0xe9, 0x24, 0x00,
	'u', 4, 6,	0x99, 0x99, 0x60,
	'v', 4, 6,	0x99, 0x96, 0x60,
	'w', 5, 6,	0x8c, 0x6b, 0x55, 0x00,
	'x', 4, 6,	0x99, 0x69, 0x90,
	'y', 3, 6,	0xb5, 0x24, 0x00,
	'z', 4, 6,	0xf2, 0x48, 0xf0,

	0,
};

// A medium font map
static const unsigned char font_map_medium [] =
{
	// Default glyph
	'.', 2, 10,	0x00, 0x3c, 0x00,

	// Tab width
	'\t', 10, 0,

	// Space
	' ', 2, 0,

	'!', 1, 10,	0xf6, 0x00,
	'(', 3, 10,	0x2a, 0x48, 0x88, 0x00,
	')', 3, 10,	0x88, 0x92, 0xa0, 0x00,
	',', 2, 10,	0x00, 0x16, 0x00,
	'-', 3, 10,	0x00, 0x70, 0x00, 0x00,
	'/', 3, 10,	0x25, 0x25, 0x20, 0x00,
	'@', 6, 10,	0x7a, 0x19, 0x6b, 0x9a, 0x07, 0x80, 0x00, 0x00,
	'$', 5, 10,	0x23, 0xab, 0x47, 0x16, 0xae, 0x20, 0x00,
	'#', 6, 10,	0x49, 0x2f, 0xd2, 0xfd, 0x24, 0x80, 0x00, 0x00,
	'%', 7, 10,	0x43, 0x49, 0x20, 0x82, 0x49, 0x61, 0x00, 0x00, 0x00,
	':', 2, 10,	0x3c, 0xf0, 0x00,
	'^', 3, 10,	0x54, 0x00, 0x00, 0x00,
	'~', 5, 10,	0x00, 0x11, 0x51, 0x00, 0x00, 0x00, 0x00,

	'0', 5, 10,	0x74, 0x73, 0x59, 0xc5, 0xc0, 0x00, 0x00,
	'1', 3, 10,	0xc9, 0x24, 0xb8, 0x00,
	'2', 5, 10,	0x74, 0x42, 0xe8, 0x43, 0xe0, 0x00, 0x00,
	'3', 5, 10,	0x74, 0x42, 0xe0, 0xc5, 0xc0, 0x00, 0x00,
	'4', 5, 10,	0x11, 0x95, 0x2f, 0x88, 0x40, 0x00, 0x00,
	'5', 5, 10,	0xfc, 0x3c, 0x10, 0xc5, 0xc0, 0x00, 0x00,
	'6', 5, 10,	0x74, 0x61, 0xe8, 0xc5, 0xc0, 0x00, 0x00,
	'7', 5, 10,	0xfc, 0x44, 0x42, 0x10, 0x80, 0x00, 0x00,
	'8', 5, 10,	0x74, 0x62, 0xe8, 0xc5, 0xc0, 0x00, 0x00,
	'9', 5, 10,	0x74, 0x62, 0xf0, 0xc5, 0xc0, 0x00, 0x00,

	'A', 6, 10,	0x31, 0x28, 0x7f, 0x86, 0x18, 0x40, 0x00, 0x00,
	'B', 6, 10,	0xfa, 0x18, 0x7e, 0x86, 0x1f, 0x80, 0x00, 0x00,
	'C', 6, 10,	0x7a, 0x18, 0x20, 0x82, 0x17, 0x80, 0x00, 0x00,
	'D', 6, 10,	0xfa, 0x18, 0x61, 0x86, 0x1f, 0x80, 0x00, 0x00,
	'E', 6, 10,	0xfe, 0x08, 0x3c, 0x82, 0x0f, 0xc0, 0x00, 0x00,
	'F', 6, 10,	0xfe, 0x08, 0x3c, 0x82, 0x08, 0x00, 0x00, 0x00,
	'G', 6, 10,	0x7a, 0x18, 0x27, 0x86, 0x17, 0xc0, 0x00, 0x00,
	'H', 6, 10,	0x86, 0x18, 0x7f, 0x86, 0x18, 0x40, 0x00, 0x00,
	'I', 3, 10,	0xe9, 0x24, 0xb8, 0x00,
	'J', 6, 10,	0xfc, 0x41, 0x04, 0x12, 0x46, 0x00, 0x00, 0x00,
	'K', 5, 10,	0x8c, 0xa9, 0x8a, 0x4a, 0x20, 0x00, 0x00,
	'L', 4, 10,	0x88, 0x88, 0x88, 0xf0, 0x00,
	'M', 6, 10,	0x87, 0x3b, 0x61, 0x86, 0x18, 0x40, 0x00, 0x00,
	'N', 5, 10,	0x8e, 0x6b, 0x38, 0xc6, 0x20, 0x00, 0x00,
	'O', 6, 10,	0x7a, 0x18, 0x61, 0x86, 0x17, 0x80, 0x00, 0x00,
	'P', 5, 10,	0xf4, 0x63, 0xe8, 0x42, 0x00, 0x00, 0x00,
	'Q', 6, 10,	0x7a, 0x18, 0x61, 0x86, 0x57, 0x81, 0x00, 0x00,
	'R', 5, 10,	0xf4, 0x63, 0xe8, 0xc6, 0x20, 0x00, 0x00,
	'S', 6, 10,	0x7a, 0x18, 0x1e, 0x06, 0x17, 0x80, 0x00, 0x00,
	'T', 3, 10,	0xe9, 0x24, 0x90, 0x00,
	'U', 6, 10,	0x86, 0x18, 0x61, 0x86, 0x17, 0x80, 0x00, 0x00,
	'V', 6, 10,	0x86, 0x18, 0x61, 0x85, 0x23, 0x00, 0x00, 0x00,
	'W', 7, 10,	0x83, 0x06, 0x4c, 0x99, 0x35, 0x51, 0x00, 0x00, 0x00,
	'X', 5, 10,	0x8c, 0x54, 0x45, 0x46, 0x20, 0x00, 0x00,
	'Y', 5, 10,	0x8c, 0x54, 0x42, 0x10, 0x80, 0x00, 0x00,
	'Z', 6, 10,	0xfc, 0x10, 0x84, 0x21, 0x0f, 0xc0, 0x00, 0x00,

	'a', 4, 10,	0x00, 0x61, 0x79, 0x70, 0x00,
	'b', 4, 10,	0x88, 0xe9, 0x99, 0xe0, 0x00,
	'c', 4, 10,	0x00, 0x78, 0x88, 0x70, 0x00,
	'd', 4, 10,	0x11, 0x79, 0x99, 0x70, 0x00,
	'e', 4, 10,	0x00, 0x69, 0xf8, 0x60, 0x00,
	'f', 4, 10,	0x25, 0x4e, 0x44, 0x40, 0x00,
	'g', 4, 10,	0x00, 0x79, 0x99, 0x71, 0x60,
	'h', 4, 10,	0x88, 0xe9, 0x99, 0x90, 0x00,
	'i', 1, 10,	0xbe, 0x00,
	'j', 2, 10,	0x04, 0x55, 0x80,
	'k', 4, 10,	0x89, 0xac, 0xca, 0x90, 0x00,
	'l', 3, 10,	0xc9, 0x24, 0x98, 0x00,
	'm', 5, 10,	0x00, 0x15, 0x5a, 0xd6, 0x20, 0x00, 0x00,
	'n', 4, 10,	0x00, 0xe9, 0x99, 0x90, 0x00,
	'o', 4, 10,	0x00, 0x69, 0x99, 0x60, 0x00,
	'p', 4, 10,	0x00, 0xe9, 0x99, 0xe8, 0x80,
	'q', 4, 10,	0x00, 0x79, 0x97, 0x11, 0x10,
	'r', 3, 10,	0x02, 0xe9, 0x20, 0x00,
	's', 4, 10,	0x00, 0x78, 0x61, 0xe0, 0x00,
	't', 3, 10,	0x4b, 0xa4, 0x88, 0x00,
	'u', 4, 10,	0x00, 0x99, 0x99, 0x70, 0x00,
	'v', 4, 10,	0x00, 0x99, 0x99, 0x60, 0x00,
	'w', 5, 10,	0x00, 0x23, 0x1a, 0xd5, 0x40, 0x00, 0x00,
	'x', 5, 10,	0x00, 0x22, 0xa2, 0x2a, 0x20, 0x00, 0x00,
	'y', 4, 10,	0x00, 0x99, 0x99, 0x71, 0x60,
	'z', 4, 10,	0x00, 0xf1, 0x24, 0xf0, 0x00,

	0,

};

const char* ezd_next_glyph( const char* pGlyph )
{
	int sz;

	// Last glyph?
	if ( !pGlyph || !*pGlyph )
		return 0;

	// Glyph size in bits
	sz = pGlyph[ 1 ] * pGlyph[ 2 ];

	// Return a pointer to the next glyph
	return &pGlyph[ 3 + ( ( sz & 0x07 ) ? ( ( sz >> 3 ) + 1 ) : sz >> 3 ) ];
}

const char* ezd_find_glyph( HEZDFONT x_pFt, const char ch )
{
#if !defined( EZD_STATIC_FONTS )

		SFontData *f = (SFontData*)x_pFt;

		// Ensure valid font pointer
		if ( !f )
			return 0;

		// Get a pointer to the glyph
		return f->pIndex[ ch ];
#else

	const char* pGlyph = (const char*)x_pFt;

	// Find the glyph
	while ( pGlyph && *pGlyph )
		if ( ch == *pGlyph )
			return pGlyph;
		else
			pGlyph = ezd_next_glyph( pGlyph );

	// First glyph is the default
	return (const char*)x_pFt;

#endif
}


HEZDFONT ezd_load_font( const void *x_pFt, int x_nFtSize, unsigned int x_uFlags )
{
#if !defined( EZD_STATIC_FONTS )

	int i, sz;
	SFontData *p;
	const unsigned char *pGlyph, *pFt = (const unsigned char*)x_pFt;

	// Font parameters
	if ( !pFt )
		return _ERR( (HEZDFONT)0, "Invalid parameters" );

	// Check for built in small font
	if ( EZD_FONT_TYPE_SMALL == pFt )
		pFt = font_map_small,  x_nFtSize = sizeof( font_map_small );

	// Check for built in large font
	else if ( EZD_FONT_TYPE_MEDIUM == pFt )
		pFt = font_map_medium, x_nFtSize = sizeof( font_map_medium );

	// Check for built in large font
	else if ( EZD_FONT_TYPE_LARGE == pFt )
		return 0;

	/// Null terminated font buffer?
	if ( 0 >= x_nFtSize )
	{	x_nFtSize = 0;
		while ( pFt[ x_nFtSize ] )
		{	sz = pFt[ x_nFtSize + 1 ] * pFt[ x_nFtSize + 2 ];
			x_nFtSize += 3 + ( ( sz & 0x07 ) ? ( ( sz >> 3 ) + 1 ) : sz >> 3 );
		} // end while
	} // end if

	// Sanity check
	if ( 0 >= x_nFtSize )
		return _ERR( (HEZDFONT)0, "Empty font table" );

	// Allocate space for font buffer
	p = (SFontData*)EZD_malloc( sizeof( SFontData ) + x_nFtSize );
	if ( !p )
		return 0;

	// Copy the font bitmaps
	EZD_MEMCPY( p->pGlyph, pFt, x_nFtSize );

	// Save font flags
	p->uFlags = x_uFlags;

	// Use the first character as the default glyph
	for( i = 0; i < 256; i++ )
		p->pIndex[ i ] = p->pGlyph;

	// Index the glyphs
	pGlyph = p->pGlyph;
	while ( pGlyph && *pGlyph )
		p->pIndex[ *pGlyph ] = pGlyph,
		pGlyph = ezd_next_glyph( pGlyph );
		
	// Return the font handle
	return (HEZDFONT)p;

#else

	// Convert type
	const unsigned char *pFt = (const unsigned char*)x_pFt;

	// Font parameters
	if ( !pFt )
		return _ERR( (HEZDFONT)0, "Invalid parameters" );

	// Check for built in small font
	if ( EZD_FONT_TYPE_SMALL == pFt )
		return (HEZDFONT)font_map_small;

	// Check for built in large font
	else if ( EZD_FONT_TYPE_MEDIUM == pFt )
		return (HEZDFONT)font_map_medium;
		
	// Check for built in large font
	else if ( EZD_FONT_TYPE_LARGE == pFt )
		return 0;

	// Just use the users raw font table pointer
	else
		return (HEZDFONT)x_pFt;

#endif
}

/// Releases the specified font
void ezd_destroy_font( HEZDFONT x_hFont )
{
#if !defined( EZD_STATIC_FONTS )

	if ( x_hFont )
		EZD_free( (SFontData*)x_hFont );

#endif
}

int ezd_text_size( HEZDFONT x_hFont, const char *x_pText, int x_nTextLen, int *pw, int *ph )
{
	int i, w, h, lw = 0, lh = 0;
	const unsigned char *pGlyph;

	// Sanity check
	if ( !x_hFont || !pw || !ph )
		return _ERR( 0, "Invalid parameters" );

	// Set all sizes to zero
	*pw = *ph = 0;

	// For each character in the string
	for ( i = 0; i < x_nTextLen || ( 0 > x_nTextLen && x_pText[ i ] ); i++ )
	{
		// Get the specified glyph
		pGlyph = ezd_find_glyph( x_hFont, x_pText[ i ] );

		switch( x_pText[ i ] )
		{
			// CR
			case '\r' :

				// Reset width, and grab current height
				w = 0; //h = lh;
				i += ezd_text_size( x_hFont, &x_pText[ i + 1 ], x_nTextLen - i - 1, &w, &lh );

				// Take the largest width / height
				*pw = ( *pw > w ) ? *pw : w;
				//lh = ( lh > h ) ? lh : h;

				break;

			// LF
			case '\n' :

				// New line
				w = 0; h = 0;
				i += ezd_text_size( x_hFont, &x_pText[ i + 1 ], x_nTextLen - i - 1, &w, &h );

				// Take the longest width
				*pw = ( *pw > w ) ? *pw : w;

				// Add the height
				*ph += h;

				break;

			// Regular character
			default :

				// Accumulate width / height
				lw += !lw ? pGlyph[ 1 ] : ( 2 + pGlyph[ 1 ] ),
				lh = ( ( pGlyph[ 2 ] > lh ) ? pGlyph[ 2 ] : lh );

				break;

		} // end switch

	} // end for

	// Take the longest width
	*pw = ( *pw > lw ) ? *pw : lw;

	// Add our line height
	*ph += lh;

	return i;
}

static void ezd_draw_bmp_cb( unsigned char *pImg, int x, int y, int sw, int pw, 
							 int inv, int bw, int bh, const unsigned char *pBmp, 
							 int col, int ch, t_ezd_set_pixel pf, void *pUser )
{
	int w, h, lx = x;
	unsigned char m = 0x80;
	unsigned char r = col & 0xff;
	unsigned char g = ( col >> 8 ) & 0xff;
	unsigned char b = ( col >> 16 ) & 0xff;
	static unsigned char xm[] = { 0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01 };

	// Draw the glyph
	for( h = 0; h < bh; h++ )
	{
		// Draw horz line
		for( w = 0; w < bw; w++ )
		{
			// Next glyph byte?
			if ( !m )
				m = 0x80, pBmp++;

			// Is this pixel on?
			if ( *pBmp & m )
				if ( !pf( pUser, lx, y, col, ch ) )
					return;

			// Next bmp bit
			m >>= 1;
		
			// Next x pixel
			lx++;
			
		} // end for
		
		// Reset x
		lx = x;
		
		// Reset y
		y++;

	} // end for

}

static void ezd_draw_bmp_1( unsigned char *pImg, int x, int y, int sw, int pw, 
							int inv, int bw, int bh, const unsigned char *pBmp, int col )
{
	int w, h, lx = x;
	unsigned char m = 0x80;
	unsigned char r = col & 0xff;
	unsigned char g = ( col >> 8 ) & 0xff;
	unsigned char b = ( col >> 16 ) & 0xff;
	static unsigned char xm[] = { 0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01 };

	// Draw the glyph
	for( h = 0; h < bh; h++ )
	{
		// Draw horz line
		for( w = 0; w < bw; w++ )
		{
			// Next glyph byte?
			if ( !m )
				m = 0x80, pBmp++;

			// Is this pixel on?
			if ( *pBmp & m )
				if ( col )
					pImg[ y * sw + ( lx >> 3 ) ] |= xm[ lx & 7 ];
				else
					pImg[ y * sw + ( lx >> 3 ) ] &= ~xm[ lx & 7 ];

			// Next bmp bit
			m >>= 1;
		
			// Next x pixel
			lx++;
			
		} // end for
		
		// Reset x
		lx = x;
		
		// Reset y
		y++;

	} // end for

}

static void ezd_draw_bmp_24( unsigned char *pImg, int sw, int pw, int inv,
							 int bw, int bh, const unsigned char *pBmp, int col )
{
	int w, h;
	unsigned char m = 0x80;
	unsigned char r = col & 0xff;
	unsigned char g = ( col >> 8 ) & 0xff;
	unsigned char b = ( col >> 16 ) & 0xff;

	// Draw the glyph
	for( h = 0; h < bh; h++ )
	{
		// Draw horz line
		for( w = 0; w < bw; w++ )
		{
			// Next glyph byte?
			if ( !m )
				m = 0x80, pBmp++;

			// Is this pixel on?
			if ( *pBmp & m )
				pImg[ 0 ] = r, pImg[ 1 ] = g, pImg[ 2 ] = b;

			// Next bmp bit
			m >>= 1;

			// Next pixel
			pImg += pw;

		} // end for

		// Next image line
		if ( 0 < inv )
			pImg += sw - ( bw * pw );
		else
			pImg -= sw + ( bw * pw );

	} // end for

}

static void ezd_draw_bmp_32( unsigned char *pImg, int sw, int pw, int inv,
							 int bw, int bh, const unsigned char *pBmp, int col )
{
	int w, h;
	unsigned char m = 0x80;

	// Draw the glyph
	for( h = 0; h < bh; h++ )
	{
		// Draw horz line
		for( w = 0; w < bw; w++ )
		{
			// Next glyph byte?
			if ( !m )
				m = 0x80, pBmp++;

			// Is this pixel on?
			if ( *pBmp & m )
				*(unsigned int*)pImg = col;

			// Next bmp bit
			m >>= 1;

			// Next pixel
			pImg += pw;

		} // end for

		// Next image line
		if ( 0 < inv )
			pImg += sw - ( bw * pw );
		else
			pImg -= sw + ( bw * pw );

	} // end for

}

int ezd_text( HEZDIMAGE x_hDib, HEZDFONT x_hFont, const char *x_pText, int x_nTextLen, int x, int y, int x_col )
{
	int w, h, sw, pw, inv, i, mh = 0, lx = x;
	const unsigned char *pGlyph;
	SImageData *p = (SImageData*)x_hDib;

#if !defined( EZD_STATIC_FONTS )
	SFontData *f = (SFontData*)x_hFont;
	if ( !f )
		return _ERR( 0, "Invalid parameters" );
#endif

	// Sanity checks
	if ( !p || sizeof( SBitmapInfoHeader ) != p->bih.biSize
		 || ( !p->pImage && !p->pfSetPixel ) )
		return _ERR( 0, "Invalid parameters" );

	// Calculate image metrics
	w = EZD_ABS( p->bih.biWidth );
	h = EZD_ABS( p->bih.biHeight );

	// Invert font?
	inv = ( ( 0 < p->bih.biHeight ? 1 : 0 )
#if !defined( EZD_STATIC_FONTS )
		  ^ ( ( f->uFlags & EZD_FONT_FLAG_INVERT ) ? 1 : 0 )
#endif
		  ) ? -1 : 1;

	// Pixel and scan width
	pw = EZD_FITTO( p->bih.biBitCount, 8 );
	sw = EZD_SCANWIDTH( w, p->bih.biBitCount, 4 );

	// For each character in the string
	for ( i = 0; i < x_nTextLen || ( 0 > x_nTextLen && x_pText[ i ] ); i++ )
	{
		// Get the specified glyph
		pGlyph = ezd_find_glyph( x_hFont, x_pText[ i ] );

		// CR, just go back to starting x pos
		if ( '\r' == x_pText[ i ] )
			lx = x;

		// LF - Back to starting x and next line
		else if ( '\n' == x_pText[ i ] )
			lx = x, y += inv * ( 1 + mh ), mh = 0;

		// Other characters
		else
		{
			// Draw this glyph if it's completely on the screen
			if ( pGlyph[ 1 ] && pGlyph[ 2 ]
				 && 0 <= lx && ( lx + pGlyph[ 1 ] ) < w
				 && 0 <= y && ( y + pGlyph[ 2 ] ) < h )
			{
				// Check for user callback function
				if ( p->pfSetPixel )
					ezd_draw_bmp_cb( p->pImage, lx, y, sw, pw, inv,
									 pGlyph[ 1 ], pGlyph[ 2 ], &pGlyph[ 3 ], 
									 x_col, x_pText[ i ], p->pfSetPixel, p->pSetPixelUser );
				
				else switch( p->bih.biBitCount )
				{
					case 1 :
						ezd_draw_bmp_1( p->pImage, lx, y, sw, pw, inv,
										pGlyph[ 1 ], pGlyph[ 2 ], &pGlyph[ 3 ], 
										EZD_COMPARE_THRESHOLD( x_col, p->colThreshold ) );
						break;

					case 24 :
						ezd_draw_bmp_24( &p->pImage[ y * sw + lx * pw ], sw, pw, inv,
										 pGlyph[ 1 ], pGlyph[ 2 ], &pGlyph[ 3 ], x_col );
						break;

					case 32 :
						ezd_draw_bmp_32( &p->pImage[ y * sw + lx * pw ], sw, pw, inv,
										 pGlyph[ 1 ], pGlyph[ 2 ], &pGlyph[ 3 ], x_col );
						break;
				} // end switch

			} // end if

			// Next character position
			lx += 2 + pGlyph[ 1 ];

			// Track max height
			mh = ( pGlyph[ 2 ] > mh ) ? pGlyph[ 2 ] : mh;

		} // end else

	} // end for

	return 1;
}

#define EZD_CNVTYPE( t, c ) case EZD_TYPE_##t : return oDst + ( (double)( ((c*)pData)[ i ] ) - oSrc ) * rDst / rSrc;
double ezd_scale_value( int i, int t, void *pData, double oSrc, double rSrc, double oDst, double rDst )
{
	switch( t )
	{
		EZD_CNVTYPE( CHAR,	 		char );
		EZD_CNVTYPE( UCHAR,			unsigned char );
		EZD_CNVTYPE( SHORT, 		short );
		EZD_CNVTYPE( USHORT,		unsigned short );
		EZD_CNVTYPE( INT, 			int );
		EZD_CNVTYPE( UINT, 			unsigned int );
		EZD_CNVTYPE( LONGLONG, 		long long );
		EZD_CNVTYPE( ULONGLONG,		unsigned long long );
		EZD_CNVTYPE( FLOAT, 		float );
		EZD_CNVTYPE( DOUBLE, 		double );
//		EZD_CNVTYPE( LONGDOUBLE,	long double );

		default :
			break;

	} // end switch

	return 0;
}

double ezd_calc_range( int t, void *pData, int nData, double *pMin, double *pMax, double *pTotal )
{
	int i;
	double v;

	// Sanity checks
	if ( !pData || 0 >= nData )
		return 0;

	// Starting point
	v = ezd_scale_value( 0, t, pData, 0, 1, 0, 1 );

	if ( pMin )
		*pMin = v;

	if ( pMax )
		*pMax = v;

	if ( pTotal )
		*pTotal = 0;

	// Figure out the range
	for ( i = 1; i < nData; i++ )
	{
		// Get element value
		v = ezd_scale_value( i, t, pData, 0, 1, 0, 1 );

		// Track minimum
		if ( pMin && v < *pMin )
			*pMin = v;

		// Track maximum
		if ( pMax && v > *pMax )
			*pMax = v;

		// Accumulate total
		if ( pTotal )
			*pTotal += v;

	} // end for

	return 1;
}

