#ifndef COMPRESSION_TYPE_HPP
#define COMPRESSION_TYPE_HPP

namespace http
{

enum compression_type
{
    no_compression,
    gzip_rfc1952,
    deflate_rfc1951
};
}

#endif // COMPRESSION_TYPE_HPP