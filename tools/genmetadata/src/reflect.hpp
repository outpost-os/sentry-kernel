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

#include <concepts>
#include <fstream>

template<typename>
struct is_tuple: std::false_type{};
template<typename ...T>
struct is_tuple<std::tuple<T...>>: std::true_type{};

template<typename T >
concept return_tuple = is_tuple<std::remove_cvref_t<T>>::value;

/**
 * @brief Reflectable concept
 *
 * A type implement reflection if there is a `reflect` public method that returns a tuple
 */
template<typename T>
concept Reflectable = requires(T t) {
    { t.reflect() } -> return_tuple;
};

template<typename MemorySpec, typename T, typename std::enable_if<std::is_scalar_v<T>, bool>::type = true>
static inline void __to_bin(T val, std::ofstream& out)
{
    constexpr auto size = MemorySpec::template size_of<T>();
    constexpr auto alignment = MemorySpec::template size_of<T>();
    constexpr std::array<char, size> zero{};
    auto current = out.tellp();
    auto padding = size - (current % alignment);

    /* Insert padding if not aligned */
    if (padding < size) {
        out.write(zero.data(), padding);
    }

    out.write(reinterpret_cast<char*>(&val), size);
}

template<typename MemorySpec>
static inline void __to_bin(job_flags_t val, std::ofstream& out)
{
    uint32_t tmp;
    std::memcpy(&tmp, &val, sizeof(val));
    __to_bin<MemorySpec>(tmp, out);
}

template<typename MemorySpec, typename T, std::size_t N>
static inline void __to_bin(std::array<T, N> val, std::ofstream& out)
{
    for (T cell: val) {
        __to_bin<MemorySpec>(cell, out);
    }
}

template<typename MemorySpec, typename Tuple, std::size_t... Is>
static inline void _to_bin(const Tuple& reflection, std::ofstream& out, std::index_sequence<Is...>)
{
    ((__to_bin<MemorySpec>(std::get<Is>(reflection), out)), ...);
}

template<typename MemorySpec, typename ...Args>
static inline void _to_bin(const std::tuple<Args...>& reflection, std::ofstream& out)
{
    _to_bin<MemorySpec>(reflection, out, std::index_sequence_for<Args...>{});
}

template<typename MemorySpec, Reflectable T>
static inline void reflect_to_bin(const T& obj, const std::string& filename) {
    std::ofstream out(filename, std::ios::binary);
    _to_bin<MemorySpec>(obj.reflect(), out);
}
