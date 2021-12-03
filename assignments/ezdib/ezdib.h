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

#pragma once

#if defined( __cplusplus )
extern "C"
{
#endif

	/// Returns the absolute value of 'n'
#	define EZD_ABS( n ) ( ( 0 <= (n) ) ? (n) : -(n) )

	/// Fits 'v' to unit size 'u'
#	define EZD_FITTO( v, u ) ( ( !(u) ) ? 0 : ( (v) / (u) ) + ( ( (v) % (u) ) ? 1 : 0 ) )

	/// Aligns 'v' on block size 'a', 'a' must be a power of 2
#	define EZD_ALIGN( v, a ) ( ( (v) + ( (a) - 1 ) ) & ( ~( (a) - 1 ) ) )

	/** Calculates scan width for a given
		\param [in] w 	-	Line width in pixels
		\param [in] bpp	-	Bits per pixel
		\param [in] a	-	Alignment block size, must be power of 2
	*/
#	define EZD_SCANWIDTH( w, bpp, a ) ( EZD_ALIGN( EZD_FITTO( EZD_ABS( (w) ) * (bpp), 8 ), (a) ) )

	/** Calculates image size for a given
		\param [in] w 	-	Line width in pixels
		\param [in] h	-	Image height in pixels
		\param [in] bpp	-	Bits per pixel
		\param [in] a	-	Alignment block size, must be power of 2
	*/
#	define EZD_IMAGE_SIZE( w, h, bpp, a ) ( EZD_SCANWIDTH( (w), (bpp), (a) ) * EZD_ABS( (h) ) )

	// Declare image handle
	struct _HEZDIMAGE;
	typedef struct _HEZDIMAGE *HEZDIMAGE;

	/// Bytes required for image header
#	define EZD_HEADER_SIZE				128
	
	/// Set this flag if you will supply your own image buffer using ezd_set_image_buffer()
#	define EZD_FLAG_USER_IMAGE_BUFFER	0x0001
	
	/// Set pixel function typedef.  Supply your own set pixel 
	/// function to support unbuffered io.
	/**
		\param [in] pUser	- User data passed to ezd_set_pixel_callback()
		\param [in] x		- X coord of pixel
		\param [in] y		- Y coord of pixel
		\param [in] c		- Pixel color
		\param [in] f		- Flags
		
		\return Return non-zero to continue the current drawing operation,
				return zero to abort.
	*/
	typedef int (*t_ezd_set_pixel)( void *pUser, int x, int y, int c, int f );
	
	/// Supply your own set pixel function to support unbuffered io.
	/**
		\param [in] x_pf	- Pointer to user set pixel callback function.
		\param [in] x_pUser	- Data passed to user callback function.
		
		If you don't need a buffer, you should pass the  
		EZD_FLAG_USER_IMAGE_BUFFER flag to ezd_create() or ezd_initialize().
		
		\return Non-zero if success, otherwise zero
	*/
	int ezd_set_pixel_callback( HEZDIMAGE x_hDib, t_ezd_set_pixel x_pf, void *x_pUser );
	
	/// Returns the size buffer required for image headers
	/**
		If you use ezd_initialize(), you should call this function to get the
		number of bytes required for the buffer.
		
		If you absolutely must user a static buffer, use EZD_HEADER_SIZE, but
		be sure and pass EZD_HEADER_SIZE as the second parameter to 
		ezd_initialize() to help detect space issues ;)
		
	*/
	int ezd_header_size();	
	
	/// Creates an empty image using a user supplied buffer
	/**
		\param [in]	 x_pBuffer	- Pointer to user buffer
		\param [in]  x_nBuffer	- Size of buffer in x_pBuffer
		\param [in]  x_lWidth	- Image width
		\param [in]  x_lHeight	- Image height
		\param [in]  x_lBpp		- Image bits per pixel
		\param [in]  x_uFlags	- Image flags
		
		x_nBuffer
		
			This parameter can be zero if you don't want to verify the buffer you
			passed in is large enough.  You should have allocated a buffer that is
			at least as large as the value returned by ezd_initialize().
		
		x_lFlags
			
			EZD_FLAG_USER_IMAGE_BUFFER	- Buffer does not include room for image data.
										  User will provide buffer later by calling
										  ezd_set_image_buffer().

		\return Image handle or NULL if failure

		\see
	*/
	HEZDIMAGE ezd_initialize( void *x_pBuffer, int x_nBuffer, int x_lWidth, int x_lHeight, int x_lBpp, unsigned int x_uFlags );
	
	/// Creates an empty image
	/**
		\param [in]  x_lWidth	- Image width
		\param [in]  x_lHeight	- Image height
		\param [in]  x_lBpp		- Image bits per pixel
		\param [in]  x_uFlags	- Image flags
		
		x_lFlags
			
			EZD_FLAG_USER_IMAGE_BUFFER	- Do not allocate memory for image data,
										  user will provide buffer by calling
										  ezd_set_image_buffer().

		\return Image handle or NULL if failure

		\see
	*/
    HEZDIMAGE ezd_create( int x_lWidth, int x_lHeight, int x_lBpp, unsigned int x_uFlags );

	/// Releases the dib handle
	void ezd_destroy( HEZDIMAGE x_hDib );

	/// Sets a pointer to the users image buffer
	/**
		\param [in] x_hDib	- Handle to a dib
		\param [in] x_pImg	- Pointer to use image buffer
		\param [in] x_nImg	- Size of the buffer in x_pImg
							  If it is not zero, it must match the size decided by 
							  ezd_crate() or the function will fail.
	
		Sets a pointer to the image data that is to be used.  The caller is
		responsible for freeing the buffer.
		
		Use this function if you wish to substitute your own image buffer or 
		used the EZD_FLAG_USER_IMAGE_BUFFER with ezd_create().
		
		Calling this function with a NULL pointer will restore the buffer
		created by ezd_create().  If you passed the EZD_FLAG_USER_IMAGE_BUFFER
		to ezd_create(), then drawing functions will fail until you provide
		a buffer.
		
	*/
	int ezd_set_image_buffer( HEZDIMAGE x_hDib, void *x_pImg, int x_nImg );	
	
	/// Writes the DIB to a file
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x_pFile		- New image filename

		\return Non zero on success
	*/
	int ezd_save( HEZDIMAGE x_hDib, const char *x_pFile );

	/// Sets the threshold color for 1 bit images
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x_col		- Threshold color
		
		Colors less than or equal to the threshold color are asigned
		a value of zero, while large colors are assigned a value of one.

		\return Non zero on success
	*/
	int ezd_set_color_threshold( HEZDIMAGE x_hDib, int x_col );

	/// Sets the specified color in the color palette
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x_idx		- Color index to set
		\param [in] x_col		- Threshold color

		Currently, this library only supports 1 bit images with
		color palettes.  So x_idx must be zero or one.

		\return Non zero on success
	*/
	int ezd_set_palette_color( HEZDIMAGE x_hDib, int x_idx, int x_col );

	/// Returns the specified color in the color palette
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x_idx		- Color index to set
		\param [in] x_col		- Threshold color

		Currently, this library only supports 1 bit images with
		color palettes.  So x_idx must be zero or one.

		\return Color of the specified palette index or zero if failure
	*/
	int ezd_get_palette_color( HEZDIMAGE x_hDib, int x_idx, int x_col );

	/// Returns the number of color entries in the palette
	int ezd_get_palette_size( HEZDIMAGE x_hDib );

	/// Returns a pointer to the palette
	int* ezd_get_palette( HEZDIMAGE x_hDib );

	/// Fills the image with the specified color
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x_col		- Fill color

		\return Non zero on success
	*/
	int ezd_fill( HEZDIMAGE x_hDib, int x_col );

	/// Returns the width of the specified image
	int ezd_get_width( HEZDIMAGE x_hDib );

	/// Returns the height of the specified image
	int ezd_get_height( HEZDIMAGE x_hDib );

	/// Returns the bits per pixel of the specified image
	int ezd_get_bpp( HEZDIMAGE x_hDib );

	/// Returns the size in bytes of the image data
	int ezd_get_image_size( HEZDIMAGE x_hDib );

	/// Returns a raw image
	void* ezd_get_image_ptr( HEZDIMAGE x_hDib );

	/// Sets the specified pixel color
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x			- X coord
		\param [in] y			- Y coord
		\param [in] x_col		- Pixel color

		\return Non zero on success
	*/
	int ezd_set_pixel( HEZDIMAGE x_hDib, int x, int y, int x_col );

	/// Returns the specified pixel color
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x			- X coord
		\param [in] y			- Y coord

		\return The color of the specified pixel
	*/
	int ezd_get_pixel( HEZDIMAGE x_hDib, int x, int y );


	/// Draws a line between the specified points
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x1			- First X coord
		\param [in] y1			- First Y coord
		\param [in] x2			- Second X coord
		\param [in] y2			- Second Y coord
		\param [in] x_col		- Line color

		\return Non zero on success
	*/
	int ezd_line( HEZDIMAGE x_hDib, int x1, int y1, int x2, int y2, int x_col );

	/// Fills the specified rectangle
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x1			- Top Left X coord
		\param [in] y1			- Top Left Y coord
		\param [in] x2			- Bottom Right X coord
		\param [in] y2			- Bottom Right Y coord
		\param [in] x_col		- Fill color

		\return Non zero on success
	*/
	int ezd_fill_rect( HEZDIMAGE x_hDib, int x1, int y1, int x2, int y2, int x_col );

	/// Outlines the specified rectangle
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x1			- Top Left X coord
		\param [in] y1			- Top Left Y coord
		\param [in] x2			- Bottom Right X coord
		\param [in] y2			- Bottom Right Y coord
		\param [in] x_col		- Line color

		\return Non zero on success
	*/
	int ezd_rect( HEZDIMAGE x_hDib, int x1, int y1, int x2, int y2, int x_col );

	/// Draw circle outline
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x			- Center X coord
		\param [in] y			- Center Y coord
		\param [in] r			- Radius
		\param [in] dStart		- Start angle
		\param [in] dEnd		- End angle
		\param [in] x_col		- Line color

		\return Non zero on success
	*/
	int ezd_arc( HEZDIMAGE x_hDib, int x, int y, int x_rad, double x_dStart, double x_dEnd, int x_col );

	/// Draw circle outline
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x			- Center X coord
		\param [in] y			- Center Y coord
		\param [in] r			- Radius
		\param [in] x_col		- Line color

		\return Non zero on success
	*/
	int ezd_circle( HEZDIMAGE x_hDib, int x, int y, int x_rad, int x_col );

	/// Flood fill starting at the specified point
	/**
		\param [in] x_hDib		- Handle to a dib
		\param [in] x			- Start X coord
		\param [in] y			- Start Y coord
		\param [in] x_bcol		- Border color
		\param [in] x_col		- Fill color
	*/
	int ezd_flood_fill( HEZDIMAGE x_hDib, int x, int y, int x_bcol, int x_col );

	//--------------------------------------------------------------
	// Font functions
	//--------------------------------------------------------------

	// Declare handle
	struct _HEZDFONT;
	typedef struct _HEZDFONT *HEZDFONT;

	// Built in small font
#	define EZD_FONT_TYPE_SMALL		((unsigned char*)1)

	// Built in medium font
#	define EZD_FONT_TYPE_MEDIUM		((unsigned char*)2)

	// Built in large font
#	define EZD_FONT_TYPE_LARGE		((unsigned char*)3)

	/// Set this flag to invert the font
#	define EZD_FONT_FLAG_INVERT		0x01

	/// Loads a font map
	/**
		\param [in] x_pFt		-	Handle to a font map
		\param [in] x_pFtSize	-	Size of the specified font table

		This function basically just copies the specified
		font map and creates and index.

		\return Returns a handle to the loaded font
	*/
	HEZDFONT ezd_load_font( const void *x_pFt, int x_nFtSize, unsigned int x_uFlags );

	/// Releases the specified font
	void ezd_destroy_font( HEZDFONT x_hFont );

	/// Returns a pointer to the next glyph in a font map
	/**
		\return A pointer to the next glyph or zero if none
	*/
	const char* ezd_next_glyph( const char* pGlyph );	
	
	/// Searchs a font table for the specified glyph
	/**
		\param [in] x_pFt	- Pointer to a null terminated font table
		\param [in] ch		- Glyph to find
		
		\return A pointer to the glyph or zero if not found
	*/
	const char* ezd_find_glyph( HEZDFONT x_pFt, const char ch );
	
	/// Draws the specified text string into the image
	/**
		\param [in] x_hDib		- Image in which to draw the text
		\param [in] x_hFont		- Font handle returned by ezd_load_font()
		\param [in] x_pText		- Text string to draw
		\param [in] x_nTextLen	- Length of the string in x_pText or zero
								  for null terminated string.
		\param [in] x			- The x coord to draw the text
		\param [in] y			- The y coord to draw the text
		\param [in] x_col		- Text color

		\return Returns non-zero on success
	*/
	int ezd_text( HEZDIMAGE x_hDib, HEZDFONT x_hFont, const char *x_pText, int x_nTextLen, int x, int y, int x_col );

	/// Calculates the size of the specified text
	/**
		\param [in] x_hFont		- Font handle returned by ezd_load_font()
		\param [in] x_pText		- Text string to draw
		\param [in] x_nTextLen	- Length of the string in x_pText or zero
								  for null terminated string.
		\param [in] pw			- Recieves the calculated width
		\param [in] ph			- Receives the calculated height

		\return Returns number of characters in the text string that were considered
	*/
	int ezd_text_size( HEZDFONT x_hFont, const char *x_pText, int x_nTextLen, int *pw, int *ph );

	//--------------------------------------------------------------
	// Graph functions
	//--------------------------------------------------------------

	// Element size
#	define EZD_TYPE_MASK_SIZE		0x00ff

		// Elements are signed values
#	define EZD_TYPE_MASK_SIGNED		0x0100

		// Array
#	define EZD_TYPE_MASK_ELEMENT	0x0200

		// Array
#	define EZD_TYPE_MASK_FLOATING	0x0400

		// Array
#	define EZD_TYPE_MASK_ARRAY		0x1000

		// Null terminated
#	define EZD_TYPE_MASK_NULLTERM	0x2000

#	define EZD_TYPE_NONE			0
#	define EZD_TYPE_SHORT			( EZD_TYPE_MASK_SIGNED | sizeof( short ) )
#	define EZD_TYPE_USHORT			( sizeof( unsigned short ) )
#	define EZD_TYPE_INT				( EZD_TYPE_MASK_SIGNED | sizeof( int ) )
#	define EZD_TYPE_UINT			( sizeof( unsigned int ) )
#	define EZD_TYPE_LONG			( EZD_TYPE_MASK_SIGNED | sizeof( long ) )
#	define EZD_TYPE_ULONG			( sizeof( unsigned long ) )
#	define EZD_TYPE_LONGLONG		( EZD_TYPE_MASK_SIGNED | sizeof( long long ) )
#	define EZD_TYPE_ULONGLONG		( sizeof( unsigned long long ) )

#	define EZD_TYPE_INT8			( EZD_TYPE_MASK_SIGNED | 1 )
#	define EZD_TYPE_UINT8			( 1 )
#	define EZD_TYPE_INT16			( EZD_TYPE_MASK_SIGNED | 2 )
#	define EZD_TYPE_UINT16			( 2 )
#	define EZD_TYPE_INT24			( EZD_TYPE_MASK_SIGNED | 3 )
#	define EZD_TYPE_UINT24			( 3 )
#	define EZD_TYPE_INT32			( EZD_TYPE_MASK_SIGNED | 4 )
#	define EZD_TYPE_UINT32			( 4 )
#	define EZD_TYPE_INT64			( EZD_TYPE_MASK_SIGNED | 8 )
#	define EZD_TYPE_UINT64			( 8 )

#	define EZD_TYPE_CHAR			( EZD_TYPE_MASK_ELEMENT | EZD_TYPE_MASK_SIGNED | sizeof( char ) )
#	define EZD_TYPE_UCHAR			( EZD_TYPE_MASK_ELEMENT | sizeof( char ) )
#	define EZD_TYPE_CHAR8			( EZD_TYPE_MASK_ELEMENT | EZD_TYPE_MASK_SIGNED | 1 )
#	define EZD_TYPE_UCHAR8			( EZD_TYPE_MASK_ELEMENT | 1 )
#	define EZD_TYPE_CHAR16			( EZD_TYPE_MASK_ELEMENT | EZD_TYPE_MASK_SIGNED | 2 )
#	define EZD_TYPE_UCHAR16			( EZD_TYPE_MASK_ELEMENT | 2 )
#	define EZD_TYPE_CHAR24			( EZD_TYPE_MASK_ELEMENT | EZD_TYPE_MASK_SIGNED | 3 )
#	define EZD_TYPE_UCHAR24			( EZD_TYPE_MASK_ELEMENT | 3 )
#	define EZD_TYPE_CHAR32			( EZD_TYPE_MASK_ELEMENT | EZD_TYPE_MASK_SIGNED | 4 )
#	define EZD_TYPE_UCHAR32			( EZD_TYPE_MASK_ELEMENT | 4 )

#	define EZD_TYPE_FLOAT			( EZD_TYPE_MASK_FLOATING | sizeof( float ) )
#	define EZD_TYPE_FLOAT32			( EZD_TYPE_MASK_FLOATING | 4 )
#	define EZD_TYPE_FLOAT64			( EZD_TYPE_MASK_FLOATING | 8 )
#	define EZD_TYPE_DOUBLE			( EZD_TYPE_MASK_FLOATING | sizeof( double ) )
#	define EZD_TYPE_LONGDOUBLE		( EZD_TYPE_MASK_FLOATING | sizeof( long double ) )


	/// Returns the scaled value of the specified array element
	/**
		\param [in] i		- Index of element in pData
		\param [in] t		- Element type
		\param [in]	pData	- Pointer to an array of type t
		\param [in] oSrc	- Source scale offset
		\param [in] rSrc	- Source scale range
		\param [in] oDst	- Destination scale offset
		\param [in] rDst	- Destination scale range
	*/
	double ezd_scale_value( int i, int t, void *pData, double oSrc, double rSrc, double oDst, double rDst );

	/// Calculates the range of the specified values
	/**
		\param [in] t		- Element type
		\param [in] pData	- Pointer to an array of type t
		\param [in] nData	- Number of elements in pData
		\param [in] pMin	- Pointer to a variable that receives the minimum
		\param [in] pMax	- Pointer to a variable that receives the maximum
	*/
	double ezd_calc_range( int t, void *pData, int nData, double *pMin, double *pMax, double *pTotal );

#if defined( __cplusplus )
};
#endif

