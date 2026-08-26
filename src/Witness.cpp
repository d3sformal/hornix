/*
 *  Copyright (c) 2026, Hornix contributors
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "Witness.hpp"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

#include <algorithm>
#include <array>
#include <chrono>
#include <cctype>
#include <fstream>
#include <iomanip>
#include <optional>
#include <random>
#include <regex>
#include <sstream>
#include <stdexcept>

namespace fs = std::filesystem;

namespace hornix {
namespace {

std::string trim(std::string value) {
    auto const is_space = [](unsigned char character) { return std::isspace(character); };
    auto const first = std::find_if_not(value.begin(), value.end(), is_space);
    auto const last = std::find_if_not(value.rbegin(), value.rend(), is_space).base();
    return first < last ? std::string(first, last) : std::string{};
}

std::string readFile(fs::path const & path) {
    std::ifstream input(path, std::ios::binary);
    if (!input) { throw std::runtime_error("Could not read file: " + path.string()); }
    std::stringstream buffer;
    buffer << input.rdbuf();
    return buffer.str();
}

std::string sha256(fs::path const & path) {
    auto const content = readFile(path);
    llvm::ArrayRef<uint8_t> bytes(reinterpret_cast<uint8_t const *>(content.data()), content.size());
    return llvm::toHex(llvm::SHA256::hash(bytes), true);
}

std::string yamlString(std::string const & value) {
    std::string escaped;
    escaped.reserve(value.size() + 2);
    escaped.push_back('"');
    for (char character : value) {
        switch (character) {
            case '\\': escaped += "\\\\"; break;
            case '"': escaped += "\\\""; break;
            case '\n': escaped += "\\n"; break;
            case '\r': escaped += "\\r"; break;
            case '\t': escaped += "\\t"; break;
            default: escaped.push_back(character); break;
        }
    }
    escaped.push_back('"');
    return escaped;
}

std::string creationTime() {
    auto const now = std::chrono::system_clock::now();
    auto const time = std::chrono::system_clock::to_time_t(now);
    std::tm utc{};
#ifdef _WIN32
    gmtime_s(&utc, &time);
#else
    gmtime_r(&time, &utc);
#endif
    std::ostringstream result;
    result << std::put_time(&utc, "%Y-%m-%dT%H:%M:%SZ");
    return result.str();
}

std::string uuidV4() {
    std::random_device seed;
    std::mt19937_64 random(seed());
    std::array<unsigned char, 16> bytes{};
    for (auto & byte : bytes) { byte = static_cast<unsigned char>(random() & 0xffu); }
    bytes[6] = static_cast<unsigned char>((bytes[6] & 0x0fu) | 0x40u);
    bytes[8] = static_cast<unsigned char>((bytes[8] & 0x3fu) | 0x80u);

    std::ostringstream result;
    result << std::hex << std::setfill('0');
    for (std::size_t index = 0; index < bytes.size(); ++index) {
        result << std::setw(2) << static_cast<unsigned>(bytes[index]);
        if (index == 3 || index == 5 || index == 7 || index == 9) { result << '-'; }
    }
    return result.str();
}

struct SourceLocation {
    std::string file_name;
    unsigned line;
    unsigned column;
};

std::string maskCommentsAndStrings(std::string const & source) {
    enum class State { Code, LineComment, BlockComment, String, Character };
    std::string result = source;
    State state = State::Code;
    bool escaped = false;
    for (std::size_t index = 0; index < source.size(); ++index) {
        char const character = source[index];
        char const next = index + 1 < source.size() ? source[index + 1] : '\0';
        switch (state) {
            case State::Code:
                if (character == '/' && next == '/') {
                    result[index++] = ' ';
                    result[index] = ' ';
                    state = State::LineComment;
                } else if (character == '/' && next == '*') {
                    result[index++] = ' ';
                    result[index] = ' ';
                    state = State::BlockComment;
                } else if (character == '"') {
                    result[index] = ' ';
                    state = State::String;
                    escaped = false;
                } else if (character == '\'') {
                    result[index] = ' ';
                    state = State::Character;
                    escaped = false;
                }
                break;
            case State::LineComment:
                if (character == '\n') {
                    state = State::Code;
                } else {
                    result[index] = ' ';
                }
                break;
            case State::BlockComment:
                if (character == '*' && next == '/') {
                    result[index++] = ' ';
                    result[index] = ' ';
                    state = State::Code;
                } else if (character != '\n') {
                    result[index] = ' ';
                }
                break;
            case State::String:
            case State::Character:
                result[index] = character == '\n' ? '\n' : ' ';
                if (!escaped && ((state == State::String && character == '"') ||
                                 (state == State::Character && character == '\''))) {
                    state = State::Code;
                }
                escaped = !escaped && character == '\\';
                if (character != '\\') { escaped = false; }
                break;
        }
    }
    return result;
}

bool isIdentifierCharacter(char character) {
    return std::isalnum(static_cast<unsigned char>(character)) || character == '_';
}

std::size_t skipWhitespace(std::string const & source, std::size_t position) {
    while (position < source.size() && std::isspace(static_cast<unsigned char>(source[position]))) { ++position; }
    return position;
}

std::optional<std::size_t> closingParenthesis(std::string const & source, std::size_t opening) {
    unsigned depth = 0;
    for (std::size_t position = opening; position < source.size(); ++position) {
        if (source[position] == '(') {
            ++depth;
        } else if (source[position] == ')') {
            if (--depth == 0) { return position; }
        }
    }
    return std::nullopt;
}

bool isFunctionDeclaration(std::string const & source, std::size_t name_position) {
    auto const statement_start = source.find_last_of(";{}", name_position == 0 ? 0 : name_position - 1);
    auto const prefix_start = statement_start == std::string::npos ? 0 : statement_start + 1;
    auto const prefix = source.substr(prefix_start, name_position - prefix_start);
    static std::regex const type_at_end(
        R"(\b(?:void|char|short|int|long|float|double|signed|unsigned|_Bool|struct|union|enum)\s*$)");
    return std::regex_search(prefix, type_at_end);
}

bool isPreprocessorDirective(std::string const & source, std::size_t position) {
    auto const line_start = source.rfind('\n', position);
    auto const first = skipWhitespace(source, line_start == std::string::npos ? 0 : line_start + 1);
    return first < source.size() && source[first] == '#';
}

SourceLocation findTargetCall(fs::path const & source, std::string const & target) {
    auto const contents = readFile(source);
    auto const code = maskCommentsAndStrings(contents);
    std::optional<SourceLocation> location;
    for (std::size_t position = 0; position + target.size() <= code.size(); ++position) {
        if (code.compare(position, target.size(), target) != 0 ||
            (position > 0 && isIdentifierCharacter(code[position - 1])) ||
            (position + target.size() < code.size() && isIdentifierCharacter(code[position + target.size()]))) {
            continue;
        }
        auto const opening = skipWhitespace(code, position + target.size());
        if (opening == code.size() || code[opening] != '(') { continue; }
        if (isPreprocessorDirective(code, position) || isFunctionDeclaration(code, position)) { continue; }
        auto const closing = closingParenthesis(code, opening);
        if (!closing.has_value()) { continue; }
        // A declarator followed by a compound statement is a function definition,
        // not the call required by an unreach-call target waypoint.
        if (skipWhitespace(code, closing.value() + 1) < code.size() &&
            code[skipWhitespace(code, closing.value() + 1)] == '{') {
            continue;
        }
        auto const line = static_cast<unsigned>(std::count(contents.begin(), contents.begin() + position, '\n') + 1);
        auto const previous_newline = contents.rfind('\n', position);
        auto const column = static_cast<unsigned>(position - (previous_newline == std::string::npos ? 0 : previous_newline + 1) + 1);
        if (location.has_value()) {
            throw std::runtime_error("Violation witness requires an unambiguous direct call to '" + target +
                                     "'; trace-based selection among multiple calls is not implemented yet.");
        }
        location = SourceLocation{source.filename().string(), line, column};
    }
    if (!location.has_value()) {
        throw std::runtime_error("Could not locate a call to '" + target + "' in " + source.string());
    }
    return location.value();
}

std::string hornixConfiguration(ViolationWitnessConfiguration const & configuration) {
    return "--integer-theory bitvectors --data-model " + configuration.data_model + " --property " +
           configuration.property_file.string();
}

} // namespace

std::string unreachCallTarget(fs::path const & property_file) {
    auto const specification = trim(readFile(property_file));
    std::regex const unreach_call("LTL\\s*\\(\\s*G\\s*!\\s*call\\s*\\(\\s*([A-Za-z_][A-Za-z0-9_]*)\\s*\\(\\s*\\)\\s*\\)\\s*\\)");
    std::smatch match;
    if (!std::regex_search(specification, match, unreach_call)) {
        throw std::runtime_error("Only unreach-call properties are supported for violation witnesses: " +
                                 property_file.string());
    }
    return match[1].str();
}

void writeViolationWitness(ViolationWitnessConfiguration const & configuration) {
    auto const specification = trim(readFile(configuration.property_file));
    auto const target = unreachCallTarget(configuration.property_file);
    auto const location = findTargetCall(configuration.input_file, target);
    auto const input_file_name = configuration.input_file.filename().string();

    std::ofstream output(configuration.output_file);
    if (!output) {
        throw std::runtime_error("Could not create witness file: " + configuration.output_file.string());
    }

    output << "- entry_type: violation_sequence\n"
           << "  metadata:\n"
           << "    format_version: " << yamlString(configuration.format_version) << "\n"
           << "    uuid: " << yamlString(uuidV4()) << "\n"
           << "    creation_time: " << yamlString(creationTime()) << "\n"
           << "    producer:\n"
           << "      name: \"Hornix\"\n"
           << "      version: \"0.2.0\"\n"
           << "      configuration: " << yamlString(hornixConfiguration(configuration)) << "\n"
           << "      command_line: " << yamlString(configuration.command_line) << "\n"
           << "    task:\n"
           << "      input_files:\n"
           << "      - " << yamlString(input_file_name) << "\n"
           << "      input_file_hashes:\n"
           << "        " << yamlString(input_file_name) << ": " << yamlString(sha256(configuration.input_file)) << "\n"
           << "      specification: " << yamlString(specification) << "\n"
           << "      data_model: " << configuration.data_model << "\n"
           << "      language: C\n"
           << "  content:\n"
           << "  - segment:\n"
           << "    - waypoint:\n"
           << "        type: target\n"
           << "        action: follow\n"
           << "        location:\n"
           << "          file_name: " << yamlString(location.file_name) << "\n"
           << "          line: " << location.line << "\n"
           << "          column: " << location.column << "\n";
}

} // namespace hornix
