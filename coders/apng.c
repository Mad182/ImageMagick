/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%                        A   PPPP   N   N   GGGG                              %
%                       A A  P   P  NN  N  G                                  %
%                      AAAAA PPPP   N N N  G  GG                              %
%                      A   A P      N  NN  G   G                              %
%                      A   A P      N   N   GGGG                              %
%                                                                             %
%                                                                             %
%              Read/Write Animated Portable Network Graphics                  %
%                                                                             %
%                              Software Design                                %
%                                    Madars                                   %
%                                     2026                                    %
%                                                                             %
%  Copyright @ 1999 ImageMagick Studio LLC, a non-profit organization         %
%  dedicated to making software imaging solutions freely available.           %
%                                                                             %
%  You may not use this file except in compliance with the License.  You may  %
%  obtain a copy of the License at                                            %
%                                                                             %
%    https://imagemagick.org/license/                                         %
%                                                                             %
%  Unless required by applicable law or agreed to in writing, software        %
%  distributed under the License is distributed on an "AS IS" BASIS,          %
%  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.   %
%  See the License for the specific language governing permissions and        %
%  limitations under the License.                                             %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%
*/

/*
  Include declarations.
*/
#include "MagickCore/studio.h"
#include "MagickCore/blob.h"
#include "MagickCore/blob-private.h"
#include "MagickCore/cache.h"
#include "MagickCore/channel.h"
#include "MagickCore/colorspace.h"
#include "MagickCore/exception.h"
#include "MagickCore/exception-private.h"
#include "MagickCore/image.h"
#include "MagickCore/image-private.h"
#include "MagickCore/list.h"
#include "MagickCore/log.h"
#include "MagickCore/magick.h"
#include "MagickCore/memory_.h"
#include "MagickCore/module.h"
#include "MagickCore/pixel-accessor.h"
#include "MagickCore/quantum-private.h"
#include "MagickCore/string_.h"
#if defined(MAGICKCORE_ZLIB_DELEGATE)
#include "zlib.h"
#endif

/*
  Forward declarations.
*/
#if defined(MAGICKCORE_ZLIB_DELEGATE)
static MagickBooleanType
  WriteAPNGImage(const ImageInfo *,Image *,ExceptionInfo *);

/*
  Typedef declarations.
*/
typedef struct _APNGFrameInfo
{
  unsigned int
    width,
    height,
    x_offset,
    y_offset;

  unsigned short
    delay_num,
    delay_den;

  unsigned char
    dispose_op,
    blend_op;

  unsigned char
    *compressed_data;

  size_t
    compressed_size,
    compressed_alloc;
} APNGFrameInfo;

/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%   R e a d A P N G I m a g e                                                 %
%                                                                             %
%                                                                             %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  ReadAPNGImage() reads an Animated Portable Network Graphics (APNG) file
%  and returns composed frames as an image sequence.
%
%  The format of the ReadAPNGImage method is:
%
%      Image *ReadAPNGImage(const ImageInfo *image_info,
%        ExceptionInfo *exception)
%
%  A description of each parameter follows:
%
%    o image_info: the image info.
%
%    o exception: return any errors or warnings in this structure.
%
*/

static inline unsigned int ReadAPNGInt(const unsigned char *p)
{
  return(((unsigned int) p[0] << 24) | ((unsigned int) p[1] << 16) |
         ((unsigned int) p[2] << 8) | (unsigned int) p[3]);
}

static inline void WriteAPNGInt(unsigned char *p,unsigned int v)
{
  p[0]=(unsigned char) ((v >> 24) & 0xff);
  p[1]=(unsigned char) ((v >> 16) & 0xff);
  p[2]=(unsigned char) ((v >> 8) & 0xff);
  p[3]=(unsigned char) (v & 0xff);
}

static inline unsigned char PaethPredictor(int a,int b,int c)
{
  int
    p,pa,pb,pc;

  p=a+b-c;
  pa=abs(p-a);
  pb=abs(p-b);
  pc=abs(p-c);
  if ((pa <= pb) && (pa <= pc))
    return((unsigned char) a);
  if (pb <= pc)
    return((unsigned char) b);
  return((unsigned char) c);
}

static int BppForColorType(unsigned char ct)
{
  switch (ct)
  {
    case 0: return(1);
    case 2: return(3);
    case 3: return(1);
    case 4: return(2);
    case 6: return(4);
    default: return(0);
  }
}

static MagickBooleanType InflateAPNGData(const unsigned char *in_data,
  size_t in_size,unsigned char **out_data,size_t *out_size)
{
  int
    ret;

  size_t
    alloc_size;

  unsigned char
    *buffer,
    *new_buffer;

  z_stream
    stream;

  alloc_size=in_size*4;
  if (alloc_size < 65536)
    alloc_size=65536;
  if (alloc_size > 256*1024*1024)
    alloc_size=256*1024*1024;
  buffer=(unsigned char *) AcquireQuantumMemory(alloc_size,sizeof(*buffer));
  if (buffer == (unsigned char *) NULL)
    return(MagickFalse);
  (void) memset(&stream,0,sizeof(stream));
  stream.next_in=(Bytef *) in_data;
  stream.avail_in=(uInt) in_size;
  if (inflateInit(&stream) != Z_OK)
    {
      buffer=(unsigned char *) RelinquishMagickMemory(buffer);
      return(MagickFalse);
    }
  *out_size=0;
  do
  {
    if (*out_size + 65536 > alloc_size)
      {
        alloc_size=alloc_size*2;
        if (alloc_size > (size_t) 1024*1024*1024)
          {
            (void) inflateEnd(&stream);
            buffer=(unsigned char *) RelinquishMagickMemory(buffer);
            return(MagickFalse);
          }
        new_buffer=(unsigned char *) ResizeMagickMemory(buffer,alloc_size);
        if (new_buffer == (unsigned char *) NULL)
          {
            (void) inflateEnd(&stream);
            buffer=(unsigned char *) RelinquishMagickMemory(buffer);
            return(MagickFalse);
          }
        buffer=new_buffer;
      }
    stream.next_out=buffer+*out_size;
    stream.avail_out=(uInt) (alloc_size-*out_size);
    ret=inflate(&stream,Z_NO_FLUSH);
    if ((ret == Z_STREAM_ERROR) || (ret == Z_DATA_ERROR) ||
        (ret == Z_MEM_ERROR))
      {
        (void) inflateEnd(&stream);
        buffer=(unsigned char *) RelinquishMagickMemory(buffer);
        return(MagickFalse);
      }
    *out_size=alloc_size-stream.avail_out;
  } while (ret != Z_STREAM_END);
  (void) inflateEnd(&stream);
  *out_data=buffer;
  return(MagickTrue);
}

static MagickBooleanType UnfilterAPNGRows(unsigned char *raw,size_t raw_size,
  unsigned int w,unsigned int h,int bpp,unsigned char **pixel_data)
{
  unsigned char
    *dst,
    ft,
    *out;

  const unsigned char
    *src;

  unsigned int
    stride,
    x,
    y;

  stride=w*(unsigned int) bpp;
  if (raw_size < (size_t) h*(1+stride))
    return(MagickFalse);
  out=(unsigned char *) AcquireQuantumMemory((size_t) h*stride,sizeof(*out));
  if (out == (unsigned char *) NULL)
    return(MagickFalse);
  for (y=0; y < h; y++)
  {
    unsigned char
      a_val,b_val,c_val;

    ft=raw[y*(1+stride)];
    src=&raw[y*(1+stride)+1];
    dst=&out[y*stride];
    for (x=0; x < stride; x++)
    {
      a_val=(x >= (unsigned int) bpp) ? dst[x-bpp] : 0;
      b_val=(y > 0) ? out[(y-1)*stride+x] : 0;
      c_val=((x >= (unsigned int) bpp) && (y > 0)) ?
        out[(y-1)*stride+x-bpp] : 0;
      switch (ft)
      {
        case 0: dst[x]=src[x]; break;
        case 1: dst[x]=(unsigned char) (src[x]+a_val); break;
        case 2: dst[x]=(unsigned char) (src[x]+b_val); break;
        case 3: dst[x]=(unsigned char) (src[x]+
          (unsigned char) (((int) a_val+(int) b_val)/2)); break;
        case 4: dst[x]=(unsigned char) (src[x]+
          PaethPredictor(a_val,b_val,c_val)); break;
        default:
          out=(unsigned char *) RelinquishMagickMemory(out);
          return(MagickFalse);
      }
    }
  }
  *pixel_data=out;
  return(MagickTrue);
}

static void ConvertToRGBA(const unsigned char *px,unsigned int w,
  unsigned int h,unsigned char ct,const unsigned char *pal,size_t pal_size,
  const unsigned char *trns,size_t trns_size,unsigned char *rgba)
{
  unsigned char
    a,b,g,r;

  unsigned int
    i,
    np;

  np=w*h;
  for (i=0; i < np; i++)
  {
    r=0;
    g=0;
    b=0;
    a=255;
    switch(ct)
    {
      case 0:
        r=g=b=px[i];
        if ((trns_size >= 2) && (px[i] == trns[1]))
          a=0;
        break;
      case 2:
        r=px[i*3]; g=px[i*3+1]; b=px[i*3+2];
        if ((trns_size >= 6) && (r == trns[1]) && (g == trns[3]) &&
            (b == trns[5]))
          a=0;
        break;
      case 3:
      {
        unsigned char
          idx;

        idx=px[i];
        if ((size_t) idx*3+2 < pal_size)
          {
            r=pal[idx*3];
            g=pal[idx*3+1];
            b=pal[idx*3+2];
          }
        a=((size_t) idx < trns_size) ? trns[idx] : 255;
        break;
      }
      case 4:
        r=g=b=px[i*2]; a=px[i*2+1];
        break;
      case 6:
        r=px[i*4]; g=px[i*4+1]; b=px[i*4+2]; a=px[i*4+3];
        break;
    }
    rgba[i*4]=r;
    rgba[i*4+1]=g;
    rgba[i*4+2]=b;
    rgba[i*4+3]=a;
  }
}

static inline void BlendOver(unsigned char *dst,const unsigned char *src)
{
  unsigned int
    da,ra,sa;

  sa=src[3];
  da=dst[3];
  if (sa == 255)
    {
      (void) memcpy(dst,src,4);
      return;
    }
  if (sa == 0)
    return;
  ra=sa*255+da*(255-sa);
  dst[0]=(unsigned char) ((src[0]*sa*255+dst[0]*da*(255-sa))/ra);
  dst[1]=(unsigned char) ((src[1]*sa*255+dst[1]*da*(255-sa))/ra);
  dst[2]=(unsigned char) ((src[2]*sa*255+dst[2]*da*(255-sa))/ra);
  dst[3]=(unsigned char) ((ra+127)/255);
}

static void DestroyAPNGFrameInfo(APNGFrameInfo *frames,size_t count)
{
  size_t
    i;

  if (frames == (APNGFrameInfo *) NULL)
    return;
  for (i=0; i < count; i++)
    if (frames[i].compressed_data != (unsigned char *) NULL)
      frames[i].compressed_data=(unsigned char *)
        RelinquishMagickMemory(frames[i].compressed_data);
  frames=(APNGFrameInfo *) RelinquishMagickMemory(frames);
}

static MagickBooleanType AppendFrameData(APNGFrameInfo *frame,
  const unsigned char *data,size_t length)
{
  if (frame->compressed_data == (unsigned char *) NULL)
    {
      frame->compressed_alloc=length+4096;
      frame->compressed_data=(unsigned char *)
        AcquireQuantumMemory(frame->compressed_alloc,
          sizeof(*frame->compressed_data));
      if (frame->compressed_data == (unsigned char *) NULL)
        return(MagickFalse);
      frame->compressed_size=0;
    }
  if (frame->compressed_size+length > frame->compressed_alloc)
    {
      unsigned char
        *new_data;

      frame->compressed_alloc=(frame->compressed_size+length)*2;
      new_data=(unsigned char *) ResizeMagickMemory(frame->compressed_data,
        frame->compressed_alloc);
      if (new_data == (unsigned char *) NULL)
        {
          frame->compressed_data=(unsigned char *) NULL;
          return(MagickFalse);
        }
      frame->compressed_data=new_data;
    }
  (void) memcpy(frame->compressed_data+frame->compressed_size,data,length);
  frame->compressed_size+=length;
  return(MagickTrue);
}

static Image *ReadAPNGImage(const ImageInfo *image_info,
  ExceptionInfo *exception)
{
  APNGFrameInfo
    *cur,
    *frames;

  Image
    *image,
    *images;

  int
    bpp;

  MagickBooleanType
    first_fctl_before_idat,
    found_actl,
    seen_idat,
    status;

  size_t
    canvas_size,
    fi,
    filesize,
    frame_count,
    frames_alloc,
    num_plays,
    pal_size,
    trns_size;

  ssize_t
    x,y;

  unsigned char
    bit_depth,
    *canvas,
    color_type,
    *data,
    *palette,
    *prev_canvas,
    *trns;

  unsigned int
    canvas_h,
    canvas_w;

  /*
    Open image file.
  */
  assert(image_info != (const ImageInfo *) NULL);
  assert(image_info->signature == MagickCoreSignature);
  assert(exception != (ExceptionInfo *) NULL);
  assert(exception->signature == MagickCoreSignature);
  if (IsEventLogging() != MagickFalse)
    (void) LogMagickEvent(TraceEvent,GetMagickModule(),"%s",
      image_info->filename);
  image=AcquireImage(image_info,exception);
  status=OpenBlob(image_info,image,ReadBinaryBlobMode,exception);
  if (status == MagickFalse)
    {
      image=DestroyImageList(image);
      return((Image *) NULL);
    }
  /*
    Read entire file into memory.
  */
  filesize=(size_t) GetBlobSize(image);
  if (filesize < 33)
    ThrowReaderException(CorruptImageError,"InsufficientImageDataInFile");
  data=(unsigned char *) AcquireQuantumMemory(filesize,sizeof(*data));
  if (data == (unsigned char *) NULL)
    ThrowReaderException(ResourceLimitError,"MemoryAllocationFailed");
  if (ReadBlob(image,filesize,data) != (ssize_t) filesize)
    {
      data=(unsigned char *) RelinquishMagickMemory(data);
      ThrowReaderException(CorruptImageError,"UnexpectedEndOfFile");
    }
  (void) CloseBlob(image);
  image=DestroyImageList(image);
  /*
    Verify PNG signature.
  */
  if (memcmp(data,"\211PNG\r\n\032\n",8) != 0)
    {
      data=(unsigned char *) RelinquishMagickMemory(data);
      ThrowReaderException(CorruptImageError,"ImproperImageHeader");
    }
  /*
    Parse APNG chunks.
  */
  canvas_w=0;
  canvas_h=0;
  bit_depth=0;
  color_type=0;
  found_actl=MagickFalse;
  first_fctl_before_idat=MagickFalse;
  seen_idat=MagickFalse;
  num_plays=0;
  palette=(unsigned char *) NULL;
  pal_size=0;
  trns=(unsigned char *) NULL;
  trns_size=0;
  frames=(APNGFrameInfo *) NULL;
  frame_count=0;
  frames_alloc=0;
  cur=(APNGFrameInfo *) NULL;
  {
    size_t
      pos;

    pos=8;
    while (pos+12 <= filesize)
    {
      unsigned int
        clen;

      const unsigned char
        *cd;

      clen=ReadAPNGInt(&data[pos]);
      cd=&data[pos+8];
      if (pos+12+(size_t) clen > filesize)
        break;
      if ((memcmp(&data[pos+4],"IHDR",4) == 0) && (clen >= 13))
        {
          canvas_w=ReadAPNGInt(cd);
          canvas_h=ReadAPNGInt(cd+4);
          if ((canvas_w == 0) || (canvas_h == 0) ||
              (canvas_w > 0x7FFFFFFF) || (canvas_h > 0x7FFFFFFF))
            {
              data=(unsigned char *) RelinquishMagickMemory(data);
              ThrowReaderException(CorruptImageError,"ImproperImageHeader");
            }
          bit_depth=cd[8];
          color_type=cd[9];
        }
      else if ((memcmp(&data[pos+4],"acTL",4) == 0) && (clen >= 8))
        {
          found_actl=MagickTrue;
          num_plays=(size_t) ReadAPNGInt(cd+4);
        }
      else if (memcmp(&data[pos+4],"PLTE",4) == 0)
        {
          palette=(unsigned char *) cd;
          pal_size=clen;
        }
      else if (memcmp(&data[pos+4],"tRNS",4) == 0)
        {
          trns=(unsigned char *) cd;
          trns_size=clen;
        }
      else if ((memcmp(&data[pos+4],"fcTL",4) == 0) && (clen >= 26))
        {
          APNGFrameInfo
            new_frame,
            *new_frames;

          if (seen_idat == MagickFalse)
            first_fctl_before_idat=MagickTrue;
          (void) memset(&new_frame,0,sizeof(new_frame));
          new_frame.width=ReadAPNGInt(cd+4);
          new_frame.height=ReadAPNGInt(cd+8);
          new_frame.x_offset=ReadAPNGInt(cd+12);
          new_frame.y_offset=ReadAPNGInt(cd+16);
          new_frame.delay_num=(unsigned short) ((cd[20] << 8) | cd[21]);
          new_frame.delay_den=(unsigned short) ((cd[22] << 8) | cd[23]);
          new_frame.dispose_op=cd[24];
          new_frame.blend_op=cd[25];
          /*
            Validate frame region fits within canvas.
          */
          if ((new_frame.width == 0) || (new_frame.height == 0) ||
              ((size_t) new_frame.x_offset+new_frame.width > canvas_w) ||
              ((size_t) new_frame.y_offset+new_frame.height > canvas_h))
            {
              pos+=12+clen;
              continue;
            }
          new_frame.compressed_data=(unsigned char *) NULL;
          new_frame.compressed_size=0;
          new_frame.compressed_alloc=0;
          /*
            Grow frames array.
          */
          if (frame_count >= frames_alloc)
            {
              frames_alloc=(frames_alloc == 0) ? 16 : frames_alloc*2;
              new_frames=(APNGFrameInfo *) ResizeMagickMemory(frames,
                frames_alloc*sizeof(*frames));
              if (new_frames == (APNGFrameInfo *) NULL)
                {
                  DestroyAPNGFrameInfo(frames,frame_count);
                  data=(unsigned char *) RelinquishMagickMemory(data);
                  ThrowReaderException(ResourceLimitError,
                    "MemoryAllocationFailed");
                }
              frames=new_frames;
            }
          frames[frame_count]=new_frame;
          cur=&frames[frame_count];
          frame_count++;
        }
      else if (memcmp(&data[pos+4],"IDAT",4) == 0)
        {
          seen_idat=MagickTrue;
          if ((cur != (APNGFrameInfo *) NULL) &&
              (first_fctl_before_idat != MagickFalse) && (frame_count == 1))
            {
              if (AppendFrameData(cur,cd,clen) == MagickFalse)
                {
                  DestroyAPNGFrameInfo(frames,frame_count);
                  data=(unsigned char *) RelinquishMagickMemory(data);
                  ThrowReaderException(ResourceLimitError,
                    "MemoryAllocationFailed");
                }
            }
        }
      else if ((memcmp(&data[pos+4],"fdAT",4) == 0) && (clen > 4))
        {
          if (cur != (APNGFrameInfo *) NULL)
            {
              if (AppendFrameData(cur,cd+4,clen-4) == MagickFalse)
                {
                  DestroyAPNGFrameInfo(frames,frame_count);
                  data=(unsigned char *) RelinquishMagickMemory(data);
                  ThrowReaderException(ResourceLimitError,
                    "MemoryAllocationFailed");
                }
            }
        }
      else if (memcmp(&data[pos+4],"IEND",4) == 0)
        break;
      pos+=12+clen;
    }
  }
  /*
    Validate APNG structure.
  */
  if ((found_actl == MagickFalse) || (frame_count == 0))
    {
      Image
        *png_image;

      ImageInfo
        *read_info;

      /*
        No acTL chunk found: this is a static PNG.  Fall back to the
        regular PNG decoder so that files renamed to .apng still work.
      */
      DestroyAPNGFrameInfo(frames,frame_count);
      read_info=CloneImageInfo(image_info);
      (void) CopyMagickString(read_info->magick,"PNG",MagickPathExtent);
      png_image=BlobToImage(read_info,data,filesize,exception);
      read_info=DestroyImageInfo(read_info);
      data=(unsigned char *) RelinquishMagickMemory(data);
      return(png_image);
    }
  if (bit_depth != 8)
    {
      DestroyAPNGFrameInfo(frames,frame_count);
      data=(unsigned char *) RelinquishMagickMemory(data);
      (void) ThrowMagickException(exception,GetMagickModule(),
        CoderError,"Only 8-bit depth APNG supported","`%s'",
        image_info->filename);
      return((Image *) NULL);
    }
  bpp=BppForColorType(color_type);
  if (bpp == 0)
    {
      DestroyAPNGFrameInfo(frames,frame_count);
      data=(unsigned char *) RelinquishMagickMemory(data);
      (void) ThrowMagickException(exception,GetMagickModule(),
        CoderError,"Unsupported APNG color type","`%s'",
        image_info->filename);
      return((Image *) NULL);
    }
  /*
    Per APNG spec: first frame dispose_op PREVIOUS -> treat as BACKGROUND.
  */
  if (frames[0].dispose_op == 2)
    frames[0].dispose_op=1;
  /*
    Compose frames onto canvas.
  */
  if ((size_t) canvas_w > SIZE_MAX / ((size_t) canvas_h * 4))
    {
      DestroyAPNGFrameInfo(frames,frame_count);
      data=(unsigned char *) RelinquishMagickMemory(data);
      ThrowReaderException(CorruptImageError,"ImproperImageHeader");
    }
  canvas_size=(size_t) canvas_w * (size_t) canvas_h * 4;
  canvas=(unsigned char *) AcquireQuantumMemory(canvas_size,sizeof(*canvas));
  prev_canvas=(unsigned char *) AcquireQuantumMemory(canvas_size,
    sizeof(*prev_canvas));
  if ((canvas == (unsigned char *) NULL) ||
      (prev_canvas == (unsigned char *) NULL))
    {
      if (canvas != (unsigned char *) NULL)
        canvas=(unsigned char *) RelinquishMagickMemory(canvas);
      if (prev_canvas != (unsigned char *) NULL)
        prev_canvas=(unsigned char *) RelinquishMagickMemory(prev_canvas);
      DestroyAPNGFrameInfo(frames,frame_count);
      data=(unsigned char *) RelinquishMagickMemory(data);
      ThrowReaderException(ResourceLimitError,"MemoryAllocationFailed");
    }
  (void) memset(canvas,0,canvas_size);
  images=(Image *) NULL;
  for (fi=0; fi < frame_count; fi++)
  {
    APNGFrameInfo
      *f;

    double
      delay_seconds;

    Image
      *frame_image;

    Quantum
      *q;

    size_t
      idx,
      raw_size;

    unsigned char
      *frame_rgba,
      *pixel_data,
      *raw;

    unsigned int
      cx,cy,fx,fy;

    unsigned short
      dden,dnum;

    f=&frames[fi];
    /*
      Save canvas for DISPOSE_OP_PREVIOUS.
    */
    if (f->dispose_op == 2)
      (void) memcpy(prev_canvas,canvas,canvas_size);
    /*
      Decompress frame data.
    */
    raw=(unsigned char *) NULL;
    raw_size=0;
    if ((f->compressed_data == (unsigned char *) NULL) ||
        (f->compressed_size == 0) ||
        (InflateAPNGData(f->compressed_data,f->compressed_size,
          &raw,&raw_size) == MagickFalse))
      {
        if (canvas != (unsigned char *) NULL)
          canvas=(unsigned char *) RelinquishMagickMemory(canvas);
        if (prev_canvas != (unsigned char *) NULL)
          prev_canvas=(unsigned char *) RelinquishMagickMemory(prev_canvas);
        DestroyAPNGFrameInfo(frames,frame_count);
        data=(unsigned char *) RelinquishMagickMemory(data);
        if (images != (Image *) NULL)
          images=DestroyImageList(images);
        (void) ThrowMagickException(exception,GetMagickModule(),
          CoderError,"APNGDecompressFailed","`%s' frame %lu",
          image_info->filename,(unsigned long) fi);
        return((Image *) NULL);
      }
    /*
      Unfilter rows.
    */
    pixel_data=(unsigned char *) NULL;
    if (UnfilterAPNGRows(raw,raw_size,f->width,f->height,bpp,
        &pixel_data) == MagickFalse)
      {
        raw=(unsigned char *) RelinquishMagickMemory(raw);
        if (canvas != (unsigned char *) NULL)
          canvas=(unsigned char *) RelinquishMagickMemory(canvas);
        if (prev_canvas != (unsigned char *) NULL)
          prev_canvas=(unsigned char *) RelinquishMagickMemory(prev_canvas);
        DestroyAPNGFrameInfo(frames,frame_count);
        data=(unsigned char *) RelinquishMagickMemory(data);
        if (images != (Image *) NULL)
          images=DestroyImageList(images);
        (void) ThrowMagickException(exception,GetMagickModule(),
          CoderError,"APNGUnfilterFailed","`%s' frame %lu",
          image_info->filename,(unsigned long) fi);
        return((Image *) NULL);
      }
    raw=(unsigned char *) RelinquishMagickMemory(raw);
    /*
      Convert to RGBA.
    */
    frame_rgba=(unsigned char *) AcquireQuantumMemory(
      (size_t) f->width * (size_t) f->height,4);
    if (frame_rgba == (unsigned char *) NULL)
      {
        pixel_data=(unsigned char *) RelinquishMagickMemory(pixel_data);
        canvas=(unsigned char *) RelinquishMagickMemory(canvas);
        prev_canvas=(unsigned char *) RelinquishMagickMemory(prev_canvas);
        DestroyAPNGFrameInfo(frames,frame_count);
        data=(unsigned char *) RelinquishMagickMemory(data);
        if (images != (Image *) NULL)
          images=DestroyImageList(images);
        ThrowReaderException(ResourceLimitError,"MemoryAllocationFailed");
      }
    ConvertToRGBA(pixel_data,f->width,f->height,color_type,
      palette,pal_size,trns,trns_size,frame_rgba);
    pixel_data=(unsigned char *) RelinquishMagickMemory(pixel_data);
    /*
      Composite onto canvas.
    */
    for (fy=0; fy < f->height; fy++)
    {
      for (fx=0; fx < f->width; fx++)
      {
        cx=f->x_offset+fx;
        cy=f->y_offset+fy;
        if ((cx >= canvas_w) || (cy >= canvas_h))
          continue;
        if (f->blend_op == 0)
          (void) memcpy(&canvas[(cy*canvas_w+cx)*4],
            &frame_rgba[(fy*f->width+fx)*4],4);
        else
          BlendOver(&canvas[(cy*canvas_w+cx)*4],
            &frame_rgba[(fy*f->width+fx)*4]);
      }
    }
    frame_rgba=(unsigned char *) RelinquishMagickMemory(frame_rgba);
    /*
      Create ImageMagick Image from canvas.
    */
    frame_image=AcquireImage(image_info,exception);
    frame_image->columns=canvas_w;
    frame_image->rows=canvas_h;
    frame_image->alpha_trait=BlendPixelTrait;
    if (SetImageExtent(frame_image,canvas_w,canvas_h,exception) == MagickFalse)
      {
        frame_image=DestroyImage(frame_image);
        canvas=(unsigned char *) RelinquishMagickMemory(canvas);
        prev_canvas=(unsigned char *) RelinquishMagickMemory(prev_canvas);
        DestroyAPNGFrameInfo(frames,frame_count);
        data=(unsigned char *) RelinquishMagickMemory(data);
        if (images != (Image *) NULL)
          images=DestroyImageList(images);
        return((Image *) NULL);
      }
    for (y=0; y < (ssize_t) canvas_h; y++)
    {
      q=QueueAuthenticPixels(frame_image,0,y,canvas_w,1,exception);
      if (q == (Quantum *) NULL)
        break;
      for (x=0; x < (ssize_t) canvas_w; x++)
      {
        idx=((size_t) y*canvas_w+(size_t) x)*4;
        SetPixelRed(frame_image,ScaleCharToQuantum(canvas[idx]),q);
        SetPixelGreen(frame_image,ScaleCharToQuantum(canvas[idx+1]),q);
        SetPixelBlue(frame_image,ScaleCharToQuantum(canvas[idx+2]),q);
        SetPixelAlpha(frame_image,ScaleCharToQuantum(canvas[idx+3]),q);
        q+=GetPixelChannels(frame_image);
      }
      if (SyncAuthenticPixels(frame_image,exception) == MagickFalse)
        break;
    }
    /*
      Set frame timing.
    */
    dnum=f->delay_num;
    dden=f->delay_den;
    if (dden == 0)
      dden=100;
    delay_seconds=(double) dnum/(double) dden;
    frame_image->ticks_per_second=100;
    frame_image->delay=(size_t) (delay_seconds*100.0+0.5);
    frame_image->scene=fi;
    frame_image->dispose=BackgroundDispose;
    if (fi == 0)
      frame_image->iterations=num_plays;
    (void) CopyMagickString(frame_image->filename,image_info->filename,
      MagickPathExtent);
    (void) CopyMagickString(frame_image->magick,"APNG",MagickPathExtent);
    if (images == (Image *) NULL)
      images=frame_image;
    else
      AppendImageToList(&images,frame_image);
    /*
      Apply dispose operation.
    */
    if (f->dispose_op == 1)
      {
        /* DISPOSE_OP_BACKGROUND: clear frame region to transparent. */
        for (fy=0; fy < f->height; fy++)
          for (fx=0; fx < f->width; fx++)
          {
            cx=f->x_offset+fx;
            cy=f->y_offset+fy;
            if ((cx < canvas_w) && (cy < canvas_h))
              (void) memset(&canvas[(cy*canvas_w+cx)*4],0,4);
          }
      }
    else if (f->dispose_op == 2)
      {
        /* DISPOSE_OP_PREVIOUS: restore canvas. */
        (void) memcpy(canvas,prev_canvas,canvas_size);
      }
  }
  canvas=(unsigned char *) RelinquishMagickMemory(canvas);
  prev_canvas=(unsigned char *) RelinquishMagickMemory(prev_canvas);
  DestroyAPNGFrameInfo(frames,frame_count);
  data=(unsigned char *) RelinquishMagickMemory(data);
  return(GetFirstImageInList(images));
}
#endif /* MAGICKCORE_ZLIB_DELEGATE */

/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%   R e g i s t e r A P N G I m a g e                                         %
%                                                                             %
%                                                                             %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  RegisterAPNGImage() adds attributes for the APNG image format to the list
%  of supported formats.
%
%  The format of the RegisterAPNGImage method is:
%
%      size_t RegisterAPNGImage(void)
%
*/
ModuleExport size_t RegisterAPNGImage(void)
{
  MagickInfo
    *entry;

  entry=AcquireMagickInfo("PNG","APNG","Animated Portable Network Graphics");
#if defined(MAGICKCORE_ZLIB_DELEGATE)
  entry->decoder=(DecodeImageHandler *) ReadAPNGImage;
  entry->encoder=(EncodeImageHandler *) WriteAPNGImage;
#endif
  entry->mime_type=ConstantString("image/apng");
  entry->flags^=CoderBlobSupportFlag;
  entry->flags|=CoderDecoderSeekableStreamFlag;
  (void) RegisterMagickInfo(entry);
  return(MagickImageCoderSignature);
}

/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%   U n r e g i s t e r A P N G I m a g e                                     %
%                                                                             %
%                                                                             %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  UnregisterAPNGImage() removes format registrations made by the APNG module
%  from the list of supported formats.
%
%  The format of the UnregisterAPNGImage method is:
%
%      UnregisterAPNGImage(void)
%
*/
ModuleExport void UnregisterAPNGImage(void)
{
  (void) UnregisterMagickInfo("APNG");
}

#if defined(MAGICKCORE_ZLIB_DELEGATE)
/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%   W r i t e A P N G I m a g e                                               %
%                                                                             %
%                                                                             %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  WriteAPNGImage() writes an image sequence as an Animated Portable Network
%  Graphics (APNG) file.
%
%  The format of the WriteAPNGImage method is:
%
%      MagickBooleanType WriteAPNGImage(const ImageInfo *image_info,
%        Image *image,ExceptionInfo *exception)
%
%  A description of each parameter follows:
%
%    o image_info: the image info.
%
%    o image: the image.
%
%    o exception: return any errors or warnings in this structure.
%
*/

static MagickBooleanType WritePNGChunk(Image *image,const char *type,
  const unsigned char *chunk_data,unsigned int length,ExceptionInfo *exception)
{
  unsigned char
    header[8];

  unsigned int
    crc;

  (void) exception;
  WriteAPNGInt(header,length);
  (void) memcpy(header+4,type,4);
  if (WriteBlob(image,8,header) != 8)
    return(MagickFalse);
  crc=crc32(0,(const Bytef *) type,4);
  if (length > 0)
    {
      if (WriteBlob(image,length,chunk_data) != (ssize_t) length)
        return(MagickFalse);
      crc=crc32(crc,chunk_data,length);
    }
  WriteAPNGInt(header,crc);
  if (WriteBlob(image,4,header) != 4)
    return(MagickFalse);
  return(MagickTrue);
}

static unsigned char *FilterAPNGRows(const unsigned char *pixels,int w,int h,
  int bpp,size_t *filtered_size)
{
  const unsigned char
    *prev,
    *row;

  int
    best_filter,
    stride,
    x,
    y;

  size_t
    opos;

  unsigned char
    *filter_buf,
    *out;

  stride=w*bpp;
  *filtered_size=(size_t) h*(1+stride);
  out=(unsigned char *) AcquireQuantumMemory(*filtered_size,sizeof(*out));
  filter_buf=(unsigned char *) AcquireQuantumMemory((size_t) 5*stride,sizeof(*filter_buf));
  if ((out == (unsigned char *) NULL) || (filter_buf == (unsigned char *) NULL))
    {
      if (out != (unsigned char *) NULL)
        out=(unsigned char *) RelinquishMagickMemory(out);
      if (filter_buf != (unsigned char *) NULL)
        filter_buf=(unsigned char *) RelinquishMagickMemory(filter_buf);
      return((unsigned char *) NULL);
    }
  opos=0;
  for (y=0; y < h; y++)
  {
    long
      best_sum = LONG_MAX,
      sum;

    unsigned char
      *f0 = filter_buf,
      *f1 = filter_buf + stride,
      *f2 = filter_buf + 2*stride,
      *f3 = filter_buf + 3*stride,
      *f4 = filter_buf + 4*stride;

    row=pixels+y*stride;
    prev=(y > 0) ? pixels+(y-1)*stride : (const unsigned char *) NULL;

    /* Filter 0: None */
    sum=0;
    for (x=0; x < stride; x++)
    {
      int val = (int) row[x];
      f0[x] = (unsigned char) val;
      sum += (val < 128) ? val : 256 - val;
    }
    best_filter = 0;
    best_sum = sum;

    /* Filter 1: Sub */
    sum=0;
    for (x=0; x < bpp; x++)
    {
      int val = (int) row[x];
      f1[x] = (unsigned char) val;
      sum += (val < 128) ? val : 256 - val;
    }
    for (x=bpp; x < stride; x++)
    {
      int val = ((int) row[x] - (int) row[x-bpp]) & 0xff;
      f1[x] = (unsigned char) val;
      sum += (val < 128) ? val : 256 - val;
    }
    if (sum < best_sum)
      {
        best_sum = sum;
        best_filter = 1;
      }

    /* Filter 2: Up */
    sum=0;
    if (prev == (const unsigned char *) NULL)
      {
        (void) memcpy(f2, f0, stride);
        sum = best_sum;
      }
    else
      {
        for (x=0; x < stride; x++)
        {
          int val = ((int) row[x] - (int) prev[x]) & 0xff;
          f2[x] = (unsigned char) val;
          sum += (val < 128) ? val : 256 - val;
        }
      }
    if (sum < best_sum)
      {
        best_sum = sum;
        best_filter = 2;
      }

    /* Filter 3: Average */
    sum=0;
    if (prev == (const unsigned char *) NULL)
      {
        (void) memcpy(f3, f1, stride);
        sum = best_sum;
      }
    else
      {
        for (x=0; x < bpp; x++)
        {
          int val = ((int) row[x] - ((int) prev[x] >> 1)) & 0xff;
          f3[x] = (unsigned char) val;
          sum += (val < 128) ? val : 256 - val;
        }
        for (x=bpp; x < stride; x++)
        {
          int val = ((int) row[x] - (((int) row[x-bpp] + (int) prev[x]) >> 1)) & 0xff;
          f3[x] = (unsigned char) val;
          sum += (val < 128) ? val : 256 - val;
        }
      }
    if (sum < best_sum)
      {
        best_sum = sum;
        best_filter = 3;
      }

    /* Filter 4: Paeth */
    sum=0;
    if (prev == (const unsigned char *) NULL)
      {
        (void) memcpy(f4, f1, stride);
        sum = best_sum;
      }
    else
      {
        for (x=0; x < bpp; x++)
        {
          int val = ((int) row[x] - (int) PaethPredictor(0, prev[x], 0)) & 0xff;
          f4[x] = (unsigned char) val;
          sum += (val < 128) ? val : 256 - val;
        }
        for (x=bpp; x < stride; x++)
        {
          int val = ((int) row[x] - (int) PaethPredictor(row[x-bpp], prev[x], prev[x-bpp])) & 0xff;
          f4[x] = (unsigned char) val;
          sum += (val < 128) ? val : 256 - val;
        }
      }
    if (sum < best_sum)
      {
        best_sum = sum;
        best_filter = 4;
      }

    out[opos++] = (unsigned char) best_filter;
    (void) memcpy(out + opos, filter_buf + best_filter * stride, stride);
    opos += stride;
  }
  filter_buf=(unsigned char *) RelinquishMagickMemory(filter_buf);
  return(out);
}

static MagickBooleanType CompressAPNGFrame(const unsigned char *pixels,int w,
  int h,int bpp,unsigned char **comp_data,size_t *comp_size)
{
  int
    ret;

  size_t
    filtered_size;

  uLongf
    comp_len;

  unsigned char
    *compressed,
    *filtered;

  filtered=FilterAPNGRows(pixels,w,h,bpp,&filtered_size);
  if (filtered == (unsigned char *) NULL)
    return(MagickFalse);
  comp_len=compressBound((uLong) filtered_size);
  compressed=(unsigned char *) AcquireQuantumMemory(comp_len,
    sizeof(*compressed));
  if (compressed == (unsigned char *) NULL)
    {
      filtered=(unsigned char *) RelinquishMagickMemory(filtered);
      return(MagickFalse);
    }
  ret=compress2(compressed,&comp_len,filtered,(uLong) filtered_size,
    Z_BEST_COMPRESSION);
  filtered=(unsigned char *) RelinquishMagickMemory(filtered);
  if (ret != Z_OK)
    {
      compressed=(unsigned char *) RelinquishMagickMemory(compressed);
      return(MagickFalse);
    }
  *comp_data=compressed;
  *comp_size=(size_t) comp_len;
  return(MagickTrue);
}

static unsigned char *GetImageRGBA(Image *image,ExceptionInfo *exception)
{
  const Quantum
    *p;

  size_t
    channels,
    idx;

  ssize_t
    a_off,
    b_off,
    g_off,
    r_off,
    x,
    y;

  unsigned char
    *rgba;

  rgba=(unsigned char *) AcquireQuantumMemory((size_t) image->columns *
    (size_t) image->rows,4);
  if (rgba == (unsigned char *) NULL)
    return((unsigned char *) NULL);
  channels=GetPixelChannels(image);
  r_off=GetPixelChannelOffset(image,RedPixelChannel);
  g_off=GetPixelChannelOffset(image,GreenPixelChannel);
  b_off=GetPixelChannelOffset(image,BluePixelChannel);
  a_off=GetPixelChannelOffset(image,AlphaPixelChannel);

  for (y=0; y < (ssize_t) image->rows; y++)
  {
    p=GetVirtualPixels(image,0,y,image->columns,1,exception);
    if (p == (const Quantum *) NULL)
      {
        rgba=(unsigned char *) RelinquishMagickMemory(rgba);
        return((unsigned char *) NULL);
      }
    idx=((size_t) y * (size_t) image->columns) * 4;
    for (x=0; x < (ssize_t) image->columns; x++)
    {
      rgba[idx]=(unsigned char) ScaleQuantumToChar(p[r_off]);
      rgba[idx+1]=(unsigned char) ScaleQuantumToChar(p[g_off]);
      rgba[idx+2]=(unsigned char) ScaleQuantumToChar(p[b_off]);
      rgba[idx+3]=(a_off < (ssize_t) channels) ?
        (unsigned char) ScaleQuantumToChar(p[a_off]) : 255;
      idx+=4;
      p+=channels;
    }
  }
  return(rgba);
}

static void CleanupFramePixels(unsigned char **frame_pixels,
  size_t frame_count)
{
  size_t
    i;

  if (frame_pixels == (unsigned char **) NULL)
    return;
  for (i=0; i < frame_count; i++)
    if (frame_pixels[i] != (unsigned char *) NULL)
      frame_pixels[i]=(unsigned char *)
        RelinquishMagickMemory(frame_pixels[i]);
  frame_pixels=(unsigned char **) RelinquishMagickMemory(frame_pixels);
}

typedef struct _APNGColor
{
  unsigned char r, g, b, a;
} APNGColor;

static size_t BuildAPNGPalette(unsigned char **frame_pixels, size_t frame_count,
  size_t np, APNGColor *palette, short *hash_head, short *hash_next)
{
  size_t
    color_count,
    fi,
    px;

  (void) memset(hash_head, -1, 65536 * sizeof(short));
  (void) memset(hash_next, -1, 256 * sizeof(short));
  color_count = 0;

  for (fi = 0; fi < frame_count; fi++)
  {
    const unsigned char *pix = frame_pixels[fi];
    for (px = 0; px < np; px++)
    {
      unsigned char r = pix[px*4];
      unsigned char g = pix[px*4+1];
      unsigned char b = pix[px*4+2];
      unsigned char a = pix[px*4+3];

      unsigned short h = (unsigned short) (((r * 33 + g) * 33 + b) * 33 + a);
      short idx = hash_head[h];
      MagickBooleanType found = MagickFalse;

      while (idx != -1)
      {
        if (palette[idx].r == r && palette[idx].g == g &&
            palette[idx].b == b && palette[idx].a == a)
        {
          found = MagickTrue;
          break;
        }
        idx = hash_next[idx];
      }

      if (found == MagickFalse)
      {
        if (color_count >= 256)
          return(0); /* Exceeds 256 unique colors */
        palette[color_count].r = r;
        palette[color_count].g = g;
        palette[color_count].b = b;
        palette[color_count].a = a;
        hash_next[color_count] = hash_head[h];
        hash_head[h] = (short) color_count;
        color_count++;
      }
    }
  }
  return(color_count);
}

static inline unsigned char LookupAPNGColorIndex(unsigned char r, unsigned char g,
  unsigned char b, unsigned char a, const short *hash_head, const short *hash_next,
  const APNGColor *palette)
{
  unsigned short h = (unsigned short) (((r * 33 + g) * 33 + b) * 33 + a);
  short idx = hash_head[h];
  while (idx != -1)
  {
    if (palette[idx].r == r && palette[idx].g == g &&
        palette[idx].b == b && palette[idx].a == a)
      return((unsigned char) idx);
    idx = hash_next[idx];
  }
  return(0);
}

static MagickBooleanType WriteAPNGImage(const ImageInfo *image_info,
  Image *image,ExceptionInfo *exception)
{
  APNGColor
    *palette;

  Image
    *next;

  int
    bpp,
    color_type;

  MagickBooleanType
    has_transparency,
    status;

  short
    *hash_head,
    *hash_next;

  size_t
    color_count,
    fi,
    frame_count,
    np,
    px;

  unsigned char
    **encoded_pixels,
    **frame_pixels;

  unsigned int
    gh,
    gw,
    seq_num;

  /*
    Open output image file.
  */
  assert(image_info != (const ImageInfo *) NULL);
  assert(image_info->signature == MagickCoreSignature);
  assert(image != (Image *) NULL);
  assert(image->signature == MagickCoreSignature);
  assert(exception != (ExceptionInfo *) NULL);
  assert(exception->signature == MagickCoreSignature);
  if (IsEventLogging() != MagickFalse)
    (void) LogMagickEvent(TraceEvent,GetMagickModule(),"%s",image->filename);
  status=OpenBlob(image_info,image,WriteBinaryBlobMode,exception);
  if (status == MagickFalse)
    return(status);
  /*
    Count frames and get canvas size from first frame.
  */
  frame_count=GetImageListLength(image);
  if (frame_count == 0)
    {
      (void) CloseBlob(image);
      return(MagickFalse);
    }
  gw=(unsigned int) image->columns;
  gh=(unsigned int) image->rows;
  np=(size_t) gw*gh;
  /*
    Convert all frames to RGBA.
  */
  frame_pixels=(unsigned char **) AcquireQuantumMemory(frame_count,
    sizeof(*frame_pixels));
  if (frame_pixels == (unsigned char **) NULL)
    {
      (void) CloseBlob(image);
      ThrowWriterException(ResourceLimitError,"MemoryAllocationFailed");
    }
  (void) memset(frame_pixels,0,frame_count*sizeof(*frame_pixels));
  fi=0;
  for (next=image; next != (Image *) NULL; next=GetNextImageInList(next))
  {
    if (next->alpha_trait != BlendPixelTrait)
      (void) SetImageAlphaChannel(next,OpaqueAlphaChannel,exception);
    else
      (void) SetImageAlphaChannel(next,ActivateAlphaChannel,exception);
    (void) TransformImageColorspace(next,sRGBColorspace,exception);
    frame_pixels[fi]=GetImageRGBA(next,exception);
    if (frame_pixels[fi] == (unsigned char *) NULL)
      {
        CleanupFramePixels(frame_pixels,frame_count);
        (void) CloseBlob(image);
        ThrowWriterException(ResourceLimitError,"MemoryAllocationFailed");
      }
    fi++;
  }
  /*
    Build palette or check transparency for RGB/RGBA.
  */
  palette=(APNGColor *) AcquireQuantumMemory(256,sizeof(*palette));
  hash_head=(short *) AcquireQuantumMemory(65536,sizeof(*hash_head));
  hash_next=(short *) AcquireQuantumMemory(256,sizeof(*hash_next));
  if ((palette == (APNGColor *) NULL) || (hash_head == (short *) NULL) ||
      (hash_next == (short *) NULL))
    {
      if (palette != (APNGColor *) NULL)
        palette=(APNGColor *) RelinquishMagickMemory(palette);
      if (hash_head != (short *) NULL)
        hash_head=(short *) RelinquishMagickMemory(hash_head);
      if (hash_next != (short *) NULL)
        hash_next=(short *) RelinquishMagickMemory(hash_next);
      CleanupFramePixels(frame_pixels,frame_count);
      (void) CloseBlob(image);
      ThrowWriterException(ResourceLimitError,"MemoryAllocationFailed");
    }
  color_count=BuildAPNGPalette(frame_pixels,frame_count,np,palette,hash_head,hash_next);

  encoded_pixels=(unsigned char **) AcquireQuantumMemory(frame_count,
    sizeof(*encoded_pixels));
  if (encoded_pixels == (unsigned char **) NULL)
    {
      palette=(APNGColor *) RelinquishMagickMemory(palette);
      hash_head=(short *) RelinquishMagickMemory(hash_head);
      hash_next=(short *) RelinquishMagickMemory(hash_next);
      CleanupFramePixels(frame_pixels,frame_count);
      (void) CloseBlob(image);
      ThrowWriterException(ResourceLimitError,"MemoryAllocationFailed");
    }
  (void) memset(encoded_pixels,0,frame_count*sizeof(*encoded_pixels));

  if (color_count > 0)
    {
      /* Palette / Indexed mode (color type 3) */
      color_type=3;
      bpp=1;
      for (fi=0; fi < frame_count; fi++)
      {
        encoded_pixels[fi]=(unsigned char *) AcquireQuantumMemory(np,sizeof(unsigned char));
        if (encoded_pixels[fi] == (unsigned char *) NULL)
          {
            CleanupFramePixels(encoded_pixels,frame_count);
            palette=(APNGColor *) RelinquishMagickMemory(palette);
            hash_head=(short *) RelinquishMagickMemory(hash_head);
            hash_next=(short *) RelinquishMagickMemory(hash_next);
            CleanupFramePixels(frame_pixels,frame_count);
            (void) CloseBlob(image);
            ThrowWriterException(ResourceLimitError,"MemoryAllocationFailed");
          }
        for (px=0; px < np; px++)
        {
          unsigned char r = frame_pixels[fi][px*4];
          unsigned char g = frame_pixels[fi][px*4+1];
          unsigned char b = frame_pixels[fi][px*4+2];
          unsigned char a = frame_pixels[fi][px*4+3];
          encoded_pixels[fi][px]=LookupAPNGColorIndex(r,g,b,a,hash_head,hash_next,palette);
        }
      }
    }
  else
    {
      /* Check if any frame has transparency */
      has_transparency=MagickFalse;
      for (fi=0; fi < frame_count; fi++)
      {
        if (has_transparency != MagickFalse)
          break;
        for (px=0; px < np; px++)
        {
          if (frame_pixels[fi][px*4+3] < 255)
            {
              has_transparency=MagickTrue;
              break;
            }
        }
      }

      if (has_transparency == MagickFalse)
        {
          /* RGB mode (color type 2) */
          color_type=2;
          bpp=3;
          for (fi=0; fi < frame_count; fi++)
          {
            encoded_pixels[fi]=(unsigned char *) AcquireQuantumMemory(np,3);
            if (encoded_pixels[fi] == (unsigned char *) NULL)
              {
                CleanupFramePixels(encoded_pixels,frame_count);
                palette=(APNGColor *) RelinquishMagickMemory(palette);
                hash_head=(short *) RelinquishMagickMemory(hash_head);
                hash_next=(short *) RelinquishMagickMemory(hash_next);
                CleanupFramePixels(frame_pixels,frame_count);
                (void) CloseBlob(image);
                ThrowWriterException(ResourceLimitError,"MemoryAllocationFailed");
              }
            for (px=0; px < np; px++)
            {
              encoded_pixels[fi][px*3]=frame_pixels[fi][px*4];
              encoded_pixels[fi][px*3+1]=frame_pixels[fi][px*4+1];
              encoded_pixels[fi][px*3+2]=frame_pixels[fi][px*4+2];
            }
          }
        }
      else
        {
          /* RGBA mode (color type 6) */
          color_type=6;
          bpp=4;
          for (fi=0; fi < frame_count; fi++)
            encoded_pixels[fi]=frame_pixels[fi];
        }
    }

  /*
    Write PNG signature.
  */
  {
    const unsigned char
      png_sig[8]={137,80,78,71,13,10,26,10};

    (void) WriteBlob(image,8,png_sig);
  }
  /*
    Write IHDR chunk.
  */
  {
    unsigned char
      ihdr[13];

    WriteAPNGInt(ihdr,gw);
    WriteAPNGInt(ihdr+4,gh);
    ihdr[8]=8;           /* bit depth */
    ihdr[9]=(unsigned char) color_type;
    ihdr[10]=0;          /* compression */
    ihdr[11]=0;          /* filter */
    ihdr[12]=0;          /* interlace */
    (void) WritePNGChunk(image,"IHDR",ihdr,13,exception);
  }
  /*
    Write PLTE and tRNS chunks if indexed color mode.
  */
  if (color_type == 3)
    {
      unsigned char
        *plte;

      size_t
        i,
        plte_len;

      plte_len=color_count*3;
      plte=(unsigned char *) AcquireQuantumMemory(plte_len,sizeof(*plte));
      if (plte != (unsigned char *) NULL)
        {
          for (i=0; i < color_count; i++)
          {
            plte[i*3]=palette[i].r;
            plte[i*3+1]=palette[i].g;
            plte[i*3+2]=palette[i].b;
          }
          (void) WritePNGChunk(image,"PLTE",plte,(unsigned int) plte_len,exception);
          plte=(unsigned char *) RelinquishMagickMemory(plte);
        }

      /* Check for tRNS chunk */
      {
        ssize_t
          last_trns = -1;

        for (i=0; i < color_count; i++)
          if (palette[i].a < 255)
            last_trns=(ssize_t) i;

        if (last_trns >= 0)
          {
            unsigned char
              *trns;

            size_t
              trns_len;

            trns_len=(size_t) (last_trns+1);
            trns=(unsigned char *) AcquireQuantumMemory(trns_len,sizeof(*trns));
            if (trns != (unsigned char *) NULL)
              {
                for (i=0; i < trns_len; i++)
                  trns[i]=palette[i].a;
                (void) WritePNGChunk(image,"tRNS",trns,(unsigned int) trns_len,exception);
                trns=(unsigned char *) RelinquishMagickMemory(trns);
              }
          }
      }
    }
  /*
    Write acTL chunk (animation control).
  */
  {
    unsigned char
      actl[8];

    unsigned int
      num_plays;

    WriteAPNGInt(actl,(unsigned int) frame_count);
    num_plays=(unsigned int) image->iterations;
    WriteAPNGInt(actl+4,num_plays);
    (void) WritePNGChunk(image,"acTL",actl,8,exception);
  }
  /*
    Write frames.
  */
  seq_num=0;
  fi=0;
  for (next=image; next != (Image *) NULL; next=GetNextImageInList(next))
  {
    double
      delay_sec;

    size_t
      comp_size;

    unsigned char
      *comp_data,
      *sub_pixels;

    unsigned int
      sub_h,
      sub_w,
      sub_x,
      sub_y;

    unsigned short
      delay_den,
      delay_num;

    /*
      Calculate delay.
    */
    delay_sec=(double) next->delay/MagickMax(1.0,(double)
      next->ticks_per_second);
    delay_num=(unsigned short) MagickMin(
      (double) (delay_sec*1000.0+0.5),65535.0);
    delay_den=1000;
    /*
      Simplify fraction.
    */
    if (delay_num > 0)
      {
        unsigned short
          a_v,b_v,t_v;

        a_v=delay_num;
        b_v=delay_den;
        while (b_v != 0)
        {
          t_v=b_v;
          b_v=(unsigned short) (a_v % b_v);
          a_v=t_v;
        }
        delay_num=(unsigned short) (delay_num/a_v);
        delay_den=(unsigned short) (delay_den/a_v);
      }

    /*
      Determine bounding box for frame sub-rectangle.
    */
    if (fi == 0)
      {
        sub_x=0;
        sub_y=0;
        sub_w=gw;
        sub_h=gh;
      }
    else
      {
        unsigned int
          max_x,max_y,min_x,min_y,x,y;

        const unsigned char
          *curr_f,
          *prev_f;

        curr_f=encoded_pixels[fi];
        prev_f=encoded_pixels[fi-1];
        min_x=gw; min_y=gh;
        max_x=0; max_y=0;

        for (y=0; y < gh; y++)
        {
          for (x=0; x < gw; x++)
          {
            size_t p_off = ((size_t) y*gw + (size_t) x) * (size_t) bpp;
            if (memcmp(&curr_f[p_off], &prev_f[p_off], bpp) != 0)
              {
                if (x < min_x) min_x = x;
                if (x > max_x) max_x = x;
                if (y < min_y) min_y = y;
                if (y > max_y) max_y = y;
              }
          }
        }

        if (min_x > max_x || min_y > max_y)
          {
            /* Frames are identical */
            sub_x=0;
            sub_y=0;
            sub_w=1;
            sub_h=1;
          }
        else
          {
            sub_x=min_x;
            sub_y=min_y;
            sub_w=max_x-min_x+1;
            sub_h=max_y-min_y+1;
          }
      }

    /*
      Extract sub-rectangle pixels.
    */
    sub_pixels=(unsigned char *) AcquireQuantumMemory((size_t) sub_w * (size_t) sub_h, (size_t) bpp);
    if (sub_pixels == (unsigned char *) NULL)
      {
        if (color_type != 6)
          CleanupFramePixels(encoded_pixels,frame_count);
        palette=(APNGColor *) RelinquishMagickMemory(palette);
        hash_head=(short *) RelinquishMagickMemory(hash_head);
        hash_next=(short *) RelinquishMagickMemory(hash_next);
        CleanupFramePixels(frame_pixels,frame_count);
        (void) CloseBlob(image);
        ThrowWriterException(ResourceLimitError,"MemoryAllocationFailed");
      }

    {
      unsigned int y;
      for (y=0; y < sub_h; y++)
      {
        size_t src_off = (((size_t) (sub_y+y)*gw) + (size_t) sub_x) * (size_t) bpp;
        size_t dst_off = ((size_t) y*sub_w) * (size_t) bpp;
        (void) memcpy(&sub_pixels[dst_off], &encoded_pixels[fi][src_off], (size_t) sub_w * (size_t) bpp);
      }
    }

    /*
      Write fcTL chunk.
    */
    {
      unsigned char
        fctl[26];

      WriteAPNGInt(fctl,seq_num);
      seq_num++;
      WriteAPNGInt(fctl+4,sub_w);
      WriteAPNGInt(fctl+8,sub_h);
      WriteAPNGInt(fctl+12,sub_x);
      WriteAPNGInt(fctl+16,sub_y);
      fctl[20]=(unsigned char) ((delay_num >> 8) & 0xff);
      fctl[21]=(unsigned char) (delay_num & 0xff);
      fctl[22]=(unsigned char) ((delay_den >> 8) & 0xff);
      fctl[23]=(unsigned char) (delay_den & 0xff);
      fctl[24]=0;  /* dispose_op: NONE */
      fctl[25]=0;  /* blend_op: SOURCE */
      (void) WritePNGChunk(image,"fcTL",fctl,26,exception);
    }
    /*
      Compress sub-rectangle frame data.
    */
    comp_data=(unsigned char *) NULL;
    comp_size=0;
    if (CompressAPNGFrame(sub_pixels,(int) sub_w,(int) sub_h,bpp,
        &comp_data,&comp_size) == MagickFalse)
      {
        sub_pixels=(unsigned char *) RelinquishMagickMemory(sub_pixels);
        if (color_type != 6)
          CleanupFramePixels(encoded_pixels,frame_count);
        palette=(APNGColor *) RelinquishMagickMemory(palette);
        hash_head=(short *) RelinquishMagickMemory(hash_head);
        hash_next=(short *) RelinquishMagickMemory(hash_next);
        CleanupFramePixels(frame_pixels,frame_count);
        (void) CloseBlob(image);
        ThrowWriterException(CoderError,"APNGCompressFailed");
      }
    sub_pixels=(unsigned char *) RelinquishMagickMemory(sub_pixels);

    if (fi == 0)
      {
        /*
          First frame: write as IDAT for backwards compatibility.
        */
        (void) WritePNGChunk(image,"IDAT",comp_data,
          (unsigned int) comp_size,exception);
      }
    else
      {
        /*
          Subsequent frames: write as fdAT with sequence number.
        */
        unsigned char
          *fdat;

        unsigned int
          fdat_len;

        fdat_len=4+(unsigned int) comp_size;
        fdat=(unsigned char *) AcquireQuantumMemory(fdat_len,sizeof(*fdat));
        if (fdat == (unsigned char *) NULL)
          {
            comp_data=(unsigned char *) RelinquishMagickMemory(comp_data);
            if (color_type != 6)
              CleanupFramePixels(encoded_pixels,frame_count);
            palette=(APNGColor *) RelinquishMagickMemory(palette);
            hash_head=(short *) RelinquishMagickMemory(hash_head);
            hash_next=(short *) RelinquishMagickMemory(hash_next);
            CleanupFramePixels(frame_pixels,frame_count);
            (void) CloseBlob(image);
            ThrowWriterException(ResourceLimitError,"MemoryAllocationFailed");
          }
        WriteAPNGInt(fdat,seq_num);
        seq_num++;
        (void) memcpy(fdat+4,comp_data,comp_size);
        (void) WritePNGChunk(image,"fdAT",fdat,fdat_len,exception);
        fdat=(unsigned char *) RelinquishMagickMemory(fdat);
      }
    comp_data=(unsigned char *) RelinquishMagickMemory(comp_data);
    fi++;
  }
  /*
    Write IEND chunk.
  */
  (void) WritePNGChunk(image,"IEND",(const unsigned char *) NULL,0,exception);
  (void) CloseBlob(image);
  /*
    Cleanup.
  */
  if (color_type != 6)
    CleanupFramePixels(encoded_pixels,frame_count);
  palette=(APNGColor *) RelinquishMagickMemory(palette);
  hash_head=(short *) RelinquishMagickMemory(hash_head);
  hash_next=(short *) RelinquishMagickMemory(hash_next);
  CleanupFramePixels(frame_pixels,frame_count);
  return(MagickTrue);
}
#endif /* MAGICKCORE_ZLIB_DELEGATE */
