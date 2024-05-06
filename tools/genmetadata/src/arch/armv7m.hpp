// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

#pragma once

#include <bit>
#include <concepts>
#include <cstdint>

#include "arch.hpp"

namespace arch {
namespace armv7m {

template<typename T>
concept IsByteAligned = IsAnyOf<T, int8_t, uint8_t, char, unsigned char, signed char, std::byte>;

template<typename T>
concept IsHalfWordAligned = IsAnyOf<T, int16_t, uint16_t>;

template<typename T>
concept IsWordAligned = IsAnyOf<T, int32_t, uint32_t>;

template<typename T>
concept IsDoubleWordAligned = IsAnyOf<T, int64_t, uint64_t>;

struct memory_spec {
    static constexpr auto endianness{std::endian::little};

    template<IsByteAligned T>
    static constexpr std::size_t size_of() { return 1; }
    template<IsHalfWordAligned T>
    static constexpr std::size_t size_of() { return 2; }
    template<IsWordAligned T>
    static constexpr std::size_t size_of() { return 4; }
    template<IsDoubleWordAligned T>
    static constexpr std::size_t size_of() { return 8; }
    template<typename T, typename std::enable_if<std::is_enum_v<T>, bool>::type = true>
    static constexpr std::size_t size_of() {
        return size_of<std::underlying_type_t<T>>();
    }

    template<IsByteAligned T>
    static constexpr std::size_t aligned() { return 1; }
    template<IsHalfWordAligned T>
    static constexpr std::size_t aligned() { return 2; }
    template<IsWordAligned T>
    static constexpr std::size_t aligned() { return 4; }
    template<IsDoubleWordAligned T>
    static constexpr std::size_t aligned() { return 8; }
    template<typename T, typename std::enable_if<std::is_enum_v<T>, bool>::type = true>
    static constexpr std::size_t aligned() {
        return aligned<std::underlying_type_t<T>>();
    }
};

} // armv7m
} // namespace arch
