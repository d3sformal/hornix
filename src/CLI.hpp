/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef CLI_HPP
#define CLI_HPP

#include <map>
#include <string>

namespace hornix {

class Options {
    std::map<std::string, std::string> options;
public:
    void addOption(std::string key, std::string value) {
        options.emplace(std::move(key), std::move(value));
    }

    [[nodiscard]] std::optional<std::string> getOption(std::string const & key) const {
        auto it = options.find(key);
        return it == options.end() ? std::nullopt : std::optional<std::string>(it->second);
    }

    [[nodiscard]] std::string getOrDefault(std::string const & key, std::string const & def) const {
        auto it = options.find(key);
        return it == options.end() ? def : it->second;
    }

    [[nodiscard]] bool hasOption(std::string const & key) const {
        auto it = options.find(key);
        return it != options.end();
    }

    static const std::string INPUT_FILE;
    static const std::string PRINT_CHC;
    static const std::string SOLVER;
};

Options parse(int argc, char * argv[]);

} // namespace hornix
#endif //CLI_HPP
