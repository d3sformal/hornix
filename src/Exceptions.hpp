/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef EXCEPTIONS_HPP
#define EXCEPTIONS_HPP

#include <exception>
#include <string>

namespace hornix {
class UnsupportedFeature final : public std::exception {
public:
    explicit UnsupportedFeature(std::string message) : message(std::move(message)) {}

    [[nodiscard]] const char * what() const noexcept override { return message.c_str(); }

private:
    std::string message;
};
} // namespace hornix

#endif //EXCEPTIONS_HPP
