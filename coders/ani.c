/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%                         AAA   N   N  IIIII                                  %
%                        A   A  NN  N    I                                    %
%                        AAAAA  N N N    I                                    %
%                        A   A  N  NN    I                                    %
%                        A   A  N   N  IIIII                                  %
%                                                                             %
%                                                                             %
%                 Read/Write Windows Animated Cursor Format                   %
%                                                                             %
%                              Software Design                                %
%                                  Antigravity                                %
%                                 August 2026                                 %
%                                                                             %
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
#include "MagickCore/artifact.h"
#include "MagickCore/blob.h"
#include "MagickCore/blob-private.h"
#include "MagickCore/cache.h"
#include "MagickCore/exception.h"
#include "MagickCore/exception-private.h"
#include "MagickCore/image.h"
#include "MagickCore/image-private.h"
#include "MagickCore/list.h"
#include "MagickCore/log.h"
#include "MagickCore/magick.h"
#include "MagickCore/memory_.h"
#include "MagickCore/module.h"
#include "MagickCore/monitor.h"
#include "MagickCore/monitor-private.h"
#include "MagickCore/option.h"
#include "MagickCore/property.h"
#include "MagickCore/quantum-private.h"
#include "MagickCore/static.h"
#include "MagickCore/string_.h"
#include "MagickCore/string-private.h"
#include "coders/ani.h"

/*
  Typedef declarations.
*/
typedef struct _ANIHeader
{
  size_t
    cbSize,
    cFrames,
    cSteps,
    cx,
    cy,
    cBitCount,
    cPlanes,
    jifRate,
    flags;
} ANIHeader;

/*
  Forward declarations.
*/
static MagickBooleanType
  WriteANIImage(const ImageInfo *,Image *,ExceptionInfo *);


/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%   R e a d A N I I m a g e                                                   %
%                                                                             %
%                                                                             %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  ReadANIImage() reads a Windows Animated Cursor (.ani) image file and
%  returns it as an Image sequence.
%
%  The format of the ReadANIImage method is:
%
%      Image *ReadANIImage(const ImageInfo *image_info,ExceptionInfo *exception)
%
%  A description of each parameter follows:
%
%    o image_info: the image info.
%
%    o exception: return any errors or warnings in this structure.
%
*/
static Image *ReadANIImage(const ImageInfo *image_info,ExceptionInfo *exception)
{
  char
    magic[4];

  Image
    *image,
    **unique_frames;

  ImageInfo
    *read_info;

  MagickBooleanType
    status;

  MagickOffsetType
    riff_end;

  size_t
    i,
    num_unique_frames,
    riff_size,
    *rate_table,
    *seq_table;

  ssize_t
    count;

  ANIHeader
    anih;

  /*
    Open image file.
  */
  assert(image_info != (const ImageInfo *) NULL);
  assert(image_info->signature == MagickCoreSignature);
  if (image_info->debug != MagickFalse)
    (void) LogMagickEvent(CoderEvent,GetMagickModule(),"%s",image_info->filename);
  assert(exception != (ExceptionInfo *) NULL);
  assert(exception->signature == MagickCoreSignature);

  image=AcquireImage(image_info,exception);
  status=OpenBlob(image_info,image,ReadBinaryBlobMode,exception);
  if (status == MagickFalse)
    return(DestroyImageList(image));

  /*
    Read RIFF header.
  */
  count=ReadBlob(image,4,(unsigned char *) magic);
  if ((count != 4) || (LocaleNCompare(magic,"RIFF",4) != 0))
    ThrowReaderException(CorruptImageError,"ImproperImageHeader");

  riff_size=(size_t) ReadBlobLSBLong(image);
  count=ReadBlob(image,4,(unsigned char *) magic);
  if ((count != 4) || (LocaleNCompare(magic,"ACON",4) != 0))
    ThrowReaderException(CorruptImageError,"ImproperImageHeader");

  riff_end=TellBlob(image)+(MagickOffsetType) riff_size-4;

  memset(&anih,0,sizeof(anih));
  anih.jifRate=10;

  rate_table=(size_t *) NULL;
  seq_table=(size_t *) NULL;
  unique_frames=(Image **) NULL;
  num_unique_frames=0;

  read_info=CloneImageInfo(image_info);
  (void) CopyMagickString(read_info->magick,"ICON",MagickPathExtent);

  /*
    Parse chunks.
  */
  while ((TellBlob(image) < riff_end) && (EOFBlob(image) == MagickFalse))
  {
    char
      chunk_id[4];

    MagickOffsetType
      chunk_data_offset,
      next_chunk_offset;

    size_t
      chunk_size;

    count=ReadBlob(image,4,(unsigned char *) chunk_id);
    if (count < 4)
      break;
    chunk_size=(size_t) ReadBlobLSBLong(image);
    chunk_data_offset=TellBlob(image);
    next_chunk_offset=chunk_data_offset+(MagickOffsetType) chunk_size +
      (MagickOffsetType) (chunk_size & 1);

    if (LocaleNCompare(chunk_id,"anih",4) == 0)
      {
        if (chunk_size >= 36)
          {
            anih.cbSize=(size_t) ReadBlobLSBLong(image);
            anih.cFrames=(size_t) ReadBlobLSBLong(image);
            anih.cSteps=(size_t) ReadBlobLSBLong(image);
            anih.cx=(size_t) ReadBlobLSBLong(image);
            anih.cy=(size_t) ReadBlobLSBLong(image);
            anih.cBitCount=(size_t) ReadBlobLSBLong(image);
            anih.cPlanes=(size_t) ReadBlobLSBLong(image);
            anih.jifRate=(size_t) ReadBlobLSBLong(image);
            anih.flags=(size_t) ReadBlobLSBLong(image);
          }
      }
    else if (LocaleNCompare(chunk_id,"rate",4) == 0)
      {
        size_t
          num_rates;

        num_rates=chunk_size/4;
        if (num_rates > 0)
          {
            rate_table=(size_t *) AcquireQuantumMemory(num_rates,sizeof(*rate_table));
            if (rate_table != (size_t *) NULL)
              {
                for (i=0; i < num_rates; i++)
                  rate_table[i]=(size_t) ReadBlobLSBLong(image);
              }
          }
      }
    else if (LocaleNCompare(chunk_id,"seq ",4) == 0)
      {
        size_t
          num_seq;

        num_seq=chunk_size/4;
        if (num_seq > 0)
          {
            seq_table=(size_t *) AcquireQuantumMemory(num_seq,sizeof(*seq_table));
            if (seq_table != (size_t *) NULL)
              {
                for (i=0; i < num_seq; i++)
                  seq_table[i]=(size_t) ReadBlobLSBLong(image);
              }
          }
      }
    else if (LocaleNCompare(chunk_id,"LIST",4) == 0)
      {
        char
          list_type[4];

        count=ReadBlob(image,4,(unsigned char *) list_type);
        if ((count == 4) && (LocaleNCompare(list_type,"fram",4) == 0))
          {
            MagickOffsetType
              list_end;

            list_end=chunk_data_offset+(MagickOffsetType) chunk_size;

            if (anih.cFrames > 0)
              {
                unique_frames=(Image **) AcquireQuantumMemory(anih.cFrames,
                  sizeof(*unique_frames));
                if (unique_frames != (Image **) NULL)
                  memset(unique_frames,0,anih.cFrames*sizeof(*unique_frames));
              }

            while ((TellBlob(image) < list_end) && (EOFBlob(image) == MagickFalse))
            {
              char
                sub_id[4];

              MagickOffsetType
                sub_data_offset,
                sub_next_offset;

              size_t
                sub_size;

              count=ReadBlob(image,4,(unsigned char *) sub_id);
              if (count < 4)
                break;
              sub_size=(size_t) ReadBlobLSBLong(image);
              sub_data_offset=TellBlob(image);
              sub_next_offset=sub_data_offset+(MagickOffsetType) sub_size +
                (MagickOffsetType) (sub_size & 1);

              if ((LocaleNCompare(sub_id,"icon",4) == 0) ||
                  (LocaleNCompare(sub_id,"anih",4) != 0))
                {
                  unsigned char
                    *frame_bytes;

                  if ((sub_size > 0) && (sub_size < GetBlobSize(image)))
                    {
                      frame_bytes=(unsigned char *) AcquireQuantumMemory(sub_size,
                        sizeof(*frame_bytes));
                      if (frame_bytes != (unsigned char *) NULL)
                        {
                          count=ReadBlob(image,sub_size,frame_bytes);
                          if (count == (ssize_t) sub_size)
                            {
                              Image
                                *icon_img;

                              icon_img=BlobToImage(read_info,frame_bytes,
                                sub_size,exception);
                              if (icon_img != (Image *) NULL)
                                {
                                  if (unique_frames != (Image **) NULL &&
                                      num_unique_frames < anih.cFrames)
                                    unique_frames[num_unique_frames++]=icon_img;
                                  else
                                    icon_img=DestroyImageList(icon_img);
                                }
                            }
                          frame_bytes=(unsigned char *) RelinquishMagickMemory(frame_bytes);
                        }
                    }
                }
              (void) SeekBlob(image,sub_next_offset,SEEK_SET);
            }
          }
      }

    (void) SeekBlob(image,next_chunk_offset,SEEK_SET);
  }

  read_info=DestroyImageInfo(read_info);

  if ((anih.cSteps == 0) && (anih.cFrames > 0))
    anih.cSteps=anih.cFrames;
  if (anih.cSteps == 0)
    anih.cSteps=num_unique_frames;

  if (num_unique_frames == 0)
    {
      if (rate_table != (size_t *) NULL)
        rate_table=(size_t *) RelinquishMagickMemory(rate_table);
      if (seq_table != (size_t *) NULL)
        seq_table=(size_t *) RelinquishMagickMemory(seq_table);
      if (unique_frames != (Image **) NULL)
        unique_frames=(Image **) RelinquishMagickMemory(unique_frames);
      ThrowReaderException(CorruptImageError,"NoFramesFoundInANIFile");
    }

  /*
    Reconstruct animation sequence.
  */
  {
    Image
      *anim_list,
      *last_image;

    anim_list=(Image *) NULL;
    last_image=(Image *) NULL;

    for (i=0; i < anih.cSteps; i++)
    {
      Image
        *frame_image;

      size_t
        frame_idx,
        step_rate;

      frame_idx=i;
      if ((seq_table != (size_t *) NULL) && (i < anih.cSteps))
        frame_idx=seq_table[i];
      if (frame_idx >= num_unique_frames)
        frame_idx=0;

      frame_image=CloneImage(unique_frames[frame_idx],0,0,MagickTrue,exception);
      if (frame_image == (Image *) NULL)
        break;

      step_rate=anih.jifRate;
      if ((rate_table != (size_t *) NULL) && (i < anih.cSteps))
        step_rate=rate_table[i];
      if (step_rate == 0)
        step_rate=1;

      frame_image->ticks_per_second=60;
      frame_image->delay=step_rate;
      frame_image->scene=i;

      if (anim_list == (Image *) NULL)
        {
          anim_list=frame_image;
          last_image=frame_image;
        }
      else
        {
          last_image->next=frame_image;
          frame_image->previous=last_image;
          last_image=frame_image;
        }
    }

    /*
      Clean up temporary unique frames & tables.
    */
    for (i=0; i < num_unique_frames; i++)
      if (unique_frames[i] != (Image *) NULL)
        unique_frames[i]=DestroyImageList(unique_frames[i]);
    if (unique_frames != (Image **) NULL)
      unique_frames=(Image **) RelinquishMagickMemory(unique_frames);
    if (rate_table != (size_t *) NULL)
      rate_table=(size_t *) RelinquishMagickMemory(rate_table);
    if (seq_table != (size_t *) NULL)
      seq_table=(size_t *) RelinquishMagickMemory(seq_table);

    (void) CloseBlob(image);
    image=DestroyImageList(image);

    if (anim_list == (Image *) NULL)
      return((Image *) NULL);

    return(GetFirstImageInList(anim_list));
  }
}

/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%   R e g i s t e r A N I I m a g e                                           %
%                                                                             %
%                                                                             %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  RegisterANIImage() adds properties for the ANI image format to the list of
%  supported formats.
%
%  The format of the RegisterANIImage method is:
%
%      size_t RegisterANIImage(void)
%
*/
ModuleExport size_t RegisterANIImage(void)
{
  MagickInfo
    *entry;

  entry=AcquireMagickInfo("ANI","ANI","Windows Animated Cursor");
  entry->decoder=(DecodeImageHandler *) ReadANIImage;
  entry->encoder=(EncodeImageHandler *) WriteANIImage;
  entry->flags|=CoderDecoderSeekableStreamFlag;
  entry->flags|=CoderEncoderSeekableStreamFlag;
  (void) RegisterMagickInfo(entry);
  return(MagickImageCoderSignature);
}

/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%   U n r e g i s t e r A N I I m a g e                                       %
%                                                                             %
%                                                                             %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  UnregisterANIImage() removes format registrations made by the ANI module.
%
%  The format of the UnregisterANIImage method is:
%
%      UnregisterANIImage(void)
%
*/
ModuleExport void UnregisterANIImage(void)
{
  (void) UnregisterMagickInfo("ANI");
}

/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                                                                             %
%                                                                             %
%   W r i t e A N I I m a g e                                                 %
%                                                                             %
%                                                                             %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  WriteANIImage() writes an animation in Windows Animated Cursor format (.ani).
%
%  The format of the WriteANIImage method is:
%
%      MagickBooleanType WriteANIImage(const ImageInfo *image_info,Image *image,
%        ExceptionInfo *exception)
%
%  A description of each parameter follows.
%
%    o image_info: the image info.
%
%    o image:  The image.
%
%    o exception: return any errors or warnings in this structure.
%
*/
static MagickBooleanType WriteANIImage(const ImageInfo *image_info,Image *image,
  ExceptionInfo *exception)
{
  Image
    *curr;

  ImageInfo
    *write_info;

  MagickBooleanType
    status;

  size_t
    cSteps,
    first_jif_rate,
    fram_list_size,
    i,
    *ico_lengths,
    *jif_rates,
    total_riff_size;

  unsigned char
    **ico_blobs;

  assert(image_info != (const ImageInfo *) NULL);
  assert(image_info->signature == MagickCoreSignature);
  assert(image != (Image *) NULL);
  assert(image->signature == MagickCoreSignature);
  assert(exception != (ExceptionInfo *) NULL);
  assert(exception->signature == MagickCoreSignature);

  cSteps=GetImageListLength(image);
  if (cSteps == 0)
    return(MagickFalse);

  status=OpenBlob(image_info,image,WriteBinaryBlobMode,exception);
  if (status == MagickFalse)
    return(status);

  ico_blobs=(unsigned char **) AcquireQuantumMemory(cSteps,sizeof(*ico_blobs));
  ico_lengths=(size_t *) AcquireQuantumMemory(cSteps,sizeof(*ico_lengths));
  jif_rates=(size_t *) AcquireQuantumMemory(cSteps,sizeof(*jif_rates));

  if ((ico_blobs == (unsigned char **) NULL) ||
      (ico_lengths == (size_t *) NULL) ||
      (jif_rates == (size_t *) NULL))
    {
      if (ico_blobs != (unsigned char **) NULL)
        ico_blobs=(unsigned char **) RelinquishMagickMemory(ico_blobs);
      if (ico_lengths != (size_t *) NULL)
        ico_lengths=(size_t *) RelinquishMagickMemory(ico_lengths);
      if (jif_rates != (size_t *) NULL)
        jif_rates=(size_t *) RelinquishMagickMemory(jif_rates);
      ThrowWriterException(ResourceLimitError,"MemoryAllocationFailed");
    }

  memset(ico_blobs,0,cSteps*sizeof(*ico_blobs));
  memset(ico_lengths,0,cSteps*sizeof(*ico_lengths));

  write_info=CloneImageInfo(image_info);
  (void) CopyMagickString(write_info->magick,"ICON",MagickPathExtent);

  curr=image;
  fram_list_size=4; /* "fram" 4 bytes */

  for (i=0; i < cSteps; i++)
  {
    size_t
      jif,
      tps;

    tps=curr->ticks_per_second;
    if (tps == 0)
      tps=100;

    jif=(curr->delay * 60 + (tps / 2)) / tps;
    if (jif == 0)
      jif=10;

    jif_rates[i]=jif;

    Image
      *frame_image;

    frame_image=CloneImage(curr,0,0,MagickTrue,exception);
    if (frame_image != (Image *) NULL)
      {
        ico_blobs[i]=(unsigned char *) ImageToBlob(write_info,frame_image,
          &ico_lengths[i],exception);
        frame_image=DestroyImage(frame_image);
      }

    if ((ico_blobs[i] == (unsigned char *) NULL) || (ico_lengths[i] == 0))
      {
        write_info=DestroyImageInfo(write_info);
        for (i=0; i < cSteps; i++)
          if (ico_blobs[i] != (unsigned char *) NULL)
            ico_blobs[i]=(unsigned char *) RelinquishMagickMemory(ico_blobs[i]);
        ico_blobs=(unsigned char **) RelinquishMagickMemory(ico_blobs);
        ico_lengths=(size_t *) RelinquishMagickMemory(ico_lengths);
        jif_rates=(size_t *) RelinquishMagickMemory(jif_rates);
        ThrowWriterException(CoderError,"UnableToEncodeIconFrame");
      }

    fram_list_size += 8 + ico_lengths[i] + (ico_lengths[i] & 1);
    curr=GetNextImageInList(curr);
  }

  write_info=DestroyImageInfo(write_info);

  first_jif_rate=jif_rates[0];

  /*
    Calculate sizes:
    Form type: 4 ("ACON")
    anih: 8 + 36 = 44
    rate: 8 + cSteps*4
    LIST (fram): 8 + fram_list_size
  */
  total_riff_size=4 + 44 + (8 + cSteps * 4) + (8 + fram_list_size);

  /*
    Write RIFF Header.
  */
  (void) WriteBlob(image,4,(const unsigned char *) "RIFF");
  (void) WriteBlobLSBLong(image,(unsigned int) total_riff_size);
  (void) WriteBlob(image,4,(const unsigned char *) "ACON");

  /*
    Write anih chunk.
  */
  (void) WriteBlob(image,4,(const unsigned char *) "anih");
  (void) WriteBlobLSBLong(image,36);
  (void) WriteBlobLSBLong(image,36); /* cbSize */
  (void) WriteBlobLSBLong(image,(unsigned int) cSteps); /* cFrames */
  (void) WriteBlobLSBLong(image,(unsigned int) cSteps); /* cSteps */
  (void) WriteBlobLSBLong(image,(unsigned int) image->columns); /* cx */
  (void) WriteBlobLSBLong(image,(unsigned int) image->rows); /* cy */
  (void) WriteBlobLSBLong(image,32); /* cBitCount */
  (void) WriteBlobLSBLong(image,1); /* cPlanes */
  (void) WriteBlobLSBLong(image,(unsigned int) first_jif_rate); /* jifRate */
  (void) WriteBlobLSBLong(image,0x01); /* flags */

  /*
    Write rate chunk.
  */
  (void) WriteBlob(image,4,(const unsigned char *) "rate");
  (void) WriteBlobLSBLong(image,(unsigned int) (cSteps * 4));
  for (i=0; i < cSteps; i++)
    (void) WriteBlobLSBLong(image,(unsigned int) jif_rates[i]);

  /*
    Write LIST fram chunk.
  */
  (void) WriteBlob(image,4,(const unsigned char *) "LIST");
  (void) WriteBlobLSBLong(image,(unsigned int) fram_list_size);
  (void) WriteBlob(image,4,(const unsigned char *) "fram");

  for (i=0; i < cSteps; i++)
  {
    (void) WriteBlob(image,4,(const unsigned char *) "icon");
    (void) WriteBlobLSBLong(image,(unsigned int) ico_lengths[i]);
    (void) WriteBlob(image,ico_lengths[i],ico_blobs[i]);
    if ((ico_lengths[i] & 1) != 0)
      (void) WriteBlobByte(image,0);
  }

  /*
    Clean up.
  */
  for (i=0; i < cSteps; i++)
    if (ico_blobs[i] != (unsigned char *) NULL)
      ico_blobs[i]=(unsigned char *) RelinquishMagickMemory(ico_blobs[i]);

  ico_blobs=(unsigned char **) RelinquishMagickMemory(ico_blobs);
  ico_lengths=(size_t *) RelinquishMagickMemory(ico_lengths);
  jif_rates=(size_t *) RelinquishMagickMemory(jif_rates);

  (void) CloseBlob(image);
  return(MagickTrue);
}
