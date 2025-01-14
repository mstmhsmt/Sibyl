# This file is part of Sibyl.
# Copyright 2014 Camille MOUGEY <camille.mougey@cea.fr>
#
# Sibyl is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# Sibyl is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with Sibyl. If not, see <http://www.gnu.org/licenses/>.


from sibyl.test.test import Test, TestSetTest


class TestStrlen(Test):

    # Test1
    my_string = "Hello, w%srld !"

    def init(self):
        self.my_addr = self._alloc_string(self.my_string)
        self._add_arg(0, self.my_addr)

    def check(self):
        result = self._get_result()

        # print(f'!!! [string.TestStrlen.check] my_addr=0x{self.my_addr:x} result={result}')

        if result != len(self.my_string):
            return False

        return self._ensure_mem(self.my_addr, self.my_string.encode('utf-8') + b"\x00")

    # Test2
    def init2(self):
        self.my_addr = self._alloc_string(self.my_string * 4)
        self._add_arg(0, self.my_addr)

    def check2(self):
        result = self._get_result()

        if result != len(self.my_string * 4):
            return False

        return self._ensure_mem(self.my_addr, self.my_string.encode('utf-8') * 4 + b"\x00")

    # Properties
    func = "strlen"
    tests = TestSetTest(init, check) & TestSetTest(init2, check2)


class TestStrnicmp(Test):

    # Test1
    my_string1 = "Hello, world !"
    my_string2 = "hEllo, workk"

    def init(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)
        self._add_arg(2, len("Hello, wor"))

    def check(self):
        result = self._get_result()

        return all([result == 0,
                    self._ensure_mem(self.my_addr1, self.my_string1.encode('utf-8')),
                    self._ensure_mem(self.my_addr2, self.my_string2.encode('utf-8'))])

    # Test2
    my_string_t2 = "hEklo, workk"

    def init2(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string_t2)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)
        self._add_arg(2, len("Hello, wor"))

    def check2(self):
        result = self._get_result()

        return all([result == 3,
                    self._ensure_mem(self.my_addr1, self.my_string1.encode('utf-8')),
                    self._ensure_mem(self.my_addr2, self.my_string2.encode('utf-8'))])

    # Properties
    func = "strnicmp"
    tests = TestSetTest(init, check) & TestSetTest(init2, check2)


class TestStrcpy(Test):

    # Test
    my_string = "Hello, world !"

    def init(self):
        self.my_addr = self._alloc_string(self.my_string)
        self.my_addr2 = self._alloc_mem(len(self.my_string) + 1, write=True)

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr)

    def check(self):
        result = self._get_result()

        return all([result == self.my_addr2,
                    self._ensure_mem(self.my_addr, self.my_string.encode('utf-8')),
                    self._ensure_mem(self.my_addr2, self.my_string.encode('utf-8'))])

    # Properties
    func = "strcpy"
    tests = TestSetTest(init, check)


class TestStrncpy(Test):

    def my_init(self, dest_size, src_string, size):
        self.my_addr = self._alloc_string(src_string)
        self.my_addr2 = self._alloc_mem(dest_size, write=True)

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr)
        self._add_arg(2, size)

    def my_check(self, string, size, sizemax):
        result = self._get_result()
        return all([result == self.my_addr2,
                    self._ensure_mem(self.my_addr, string.encode('utf-8') + b"\x00"),
                    self._ensure_mem(self.my_addr2, string[:size].encode('utf-8')),
                    not(self._ensure_mem(self.my_addr2 + size,
                                         string[size:sizemax].encode('utf-8')))])

    # Test
    my_string = "Hello, world !Hello, world !Hello, world !Hello, world !"
    size_checked = 45

    def init(self):
        self.my_init(self.size_checked, self.my_string, self.size_checked)

    def check(self):
        return self.my_check(self.my_string, self.size_checked,
                             len(self.my_string) + 1)

    # Test2
    # TODO XXX: may check padding?
    my_string2 = "Hello, world !Hel\x00lo, world !Hello, world !Hello, world !"
    size_checked2 = 41

    def init2(self):
        self.real_size = self.my_string2.find("\x00") + 1
        self.my_init(self.size_checked2, self.my_string2, self.size_checked2)

    def check2(self):
        return self.my_check(self.my_string2, self.real_size,
                             self.real_size + 10)

    # Properties
    func = "strncpy"
    tests = TestSetTest(init, check) & TestSetTest(init2, check2)


class TestStrcat(Test):

    # Test
    my_string = "Hello,"
    my_string2 = " world !"

    def init(self):
        self.my_addr = self._alloc_mem(len(self.my_string) +
                                       len(self.my_string2) + 1,
                                       write=True)
        self._write_string(self.my_addr, self.my_string)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr)
        self._add_arg(1, self.my_addr2)

    def check(self):
        result = self._get_result()

        return all([result == self.my_addr,
                    self._ensure_mem(self.my_addr,
                                     self.my_string.encode('utf-8') +
                                     self.my_string2.encode('utf-8')),
                    self._ensure_mem(self.my_addr2, self.my_string2.encode('utf-8'))])

    # Properties
    func = "strcat"
    tests = TestSetTest(init, check)


class TestStrncat(Test):

    # Test
    my_string = "Hello,"
    my_string2 = " world !"
    size_trunc = 3

    def init(self):
        self.total_len = len(self.my_string) + self.size_trunc
        self.my_addr = self._alloc_mem(self.total_len + 1,
                                       write=True)
        self._write_string(self.my_addr, self.my_string)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr)
        self._add_arg(1, self.my_addr2)
        self._add_arg(2, self.size_trunc)

    def check(self):
        concated = (self.my_string + self.my_string2)[:self.total_len] + "\x00"
        return all([self._get_result() == self.my_addr,
                    self._ensure_mem(self.my_addr,
                                     concated.encode('utf-8')),
                    self._ensure_mem(self.my_addr2, self.my_string2.encode('utf-8'))])

    # Properties
    func = "strncat"
    tests = TestSetTest(init, check)


def cmp(a, b):
    return (a > b) - (a < b)


class TestStrcmp(Test):

    def my_check(self, addr1, addr2, str1, str2):
        result = self._get_result()
        result = self._to_int(result)

        if result < 0:
            result = -1
        elif result > 0:
            result = 1

        if "\x00" in str1:
            str1 = str1.split('\x00')[0]
        if "\x00" in str2:
            str2 = str2.split('\x00')[0]

        return all([result == cmp(str1+"\x00", str2+"\x00"),
                    self._ensure_mem(addr1, str1.encode('utf-8')),
                    self._ensure_mem(addr2, str2.encode('utf-8'))])

    # Test
    my_string1 = "Hello,"
    my_string2 = "Hello world !"
    my_string3 = "hello,"

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)

    def check1(self):
        return self.my_check(self.my_addr1, self.my_addr2,
                             self.my_string1, self.my_string2)

    # Test2
    def init2(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr1)

    def check2(self):
        return self.my_check(self.my_addr2, self.my_addr1,
                             self.my_string2, self.my_string1)

    # Test3
    def init3(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr3 = self._alloc_string(self.my_string1)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr3)

    def check3(self):
        return self.my_check(self.my_addr1, self.my_addr3,
                             self.my_string1, self.my_string1)

    # Test (avoid stricmp confusion)
    def init4(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr3 = self._alloc_string(self.my_string3)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr3)

    def check4(self):
        return self.my_check(self.my_addr1, self.my_addr3,
                             self.my_string1, self.my_string3)

    # Properties
    func = "strcmp"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2) & \
        TestSetTest(init3, check3) & TestSetTest(init4, check4)


class TestStrncmp(Test):

    def my_check(self, addr1, addr2, length, str1, str2):
        result = self._get_result()
        result = self._to_int(result)

        if result < 0:
            result = -1
        elif result > 0:
            result = 1

        if "\x00" in str1:
            str1 = str1.split('\x00')[0]
        if "\x00" in str2:
            str2 = str2.split('\x00')[0]
        return all([result == cmp(str1[:length], str2[:length]),
                    self._ensure_mem(addr1, str1.encode('utf-8')),
                    self._ensure_mem(addr2, str2.encode('utf-8'))])

    # Test
    my_string1 = "Hello,"
    my_string2 = "Hello world !"
    my_string3 = "hello,"
    my_string4 = "Hel"
    my_string5 = "Hel\x001o"
    my_string6 = "Hel\x002o"
    my_len = 6

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)
        self._add_arg(2, self.my_len)

    def check1(self):
        return self.my_check(self.my_addr1, self.my_addr2,
                             self.my_len,
                             self.my_string1, self.my_string2)

    # Test2
    def init2(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr1)
        self._add_arg(2, self.my_len - 1)  # Avoid strcmp confusion

    def check2(self):
        return self.my_check(self.my_addr2, self.my_addr1,
                             self.my_len - 1,
                             self.my_string2, self.my_string1)

    # Test3
    def init3(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr3 = self._alloc_string(self.my_string1)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr3)
        self._add_arg(2, self.my_len)

    def check3(self):
        return self.my_check(self.my_addr1, self.my_addr3,
                             self.my_len,
                             self.my_string1, self.my_string1)

    # Test (avoid stricmp confusion)
    def init4(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr3 = self._alloc_string(self.my_string3)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr3)
        self._add_arg(2, self.my_len)

    def check4(self):
        return self.my_check(self.my_addr1, self.my_addr3,
                             self.my_len,
                             self.my_string1, self.my_string3)

    # Test4
    def init5(self):
        self.my_addr1 = self._alloc_string(self.my_string5)
        self.my_addr2 = self._alloc_string(self.my_string6)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)
        self._add_arg(2, self.my_len)

    def check5(self):
        return self.my_check(self.my_addr1, self.my_addr2,
                             self.my_len,
                             self.my_string5, self.my_string6)

    # Properties
    func = "strncmp"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2) & \
        TestSetTest(init3, check3) & TestSetTest(init4, check4) & \
        TestSetTest(init5, check5)


class TestStricmp(Test):

    def my_check(self, addr1, addr2, str1, str2):
        result = self._get_result()
        result = self._to_int(result)

        if result < 0:
            result = -1
        elif result > 0:
            result = 1

        if "\x00" in str1:
            str1 = str1.split('\x00')[0]
        if "\x00" in str2:
            str2 = str2.split('\x00')[0]

        return all([result == cmp(str1.lower()+"\x00", str2.lower()+"\x00"),
                    self._ensure_mem(addr1, str1.encode('utf-8')),
                    self._ensure_mem(addr2, str2.encode('utf-8'))])

    # Test
    my_string1 = "Hello,"
    my_string2 = "Hello world !"
    my_string3 = "hello,"

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)

    def check1(self):
        return self.my_check(self.my_addr1, self.my_addr2,
                             self.my_string1, self.my_string2)

    # Test2
    def init2(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr1)

    def check2(self):
        return self.my_check(self.my_addr2, self.my_addr1,
                             self.my_string2, self.my_string1)

    # Test3
    def init3(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr3 = self._alloc_string(self.my_string1)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr3)

    def check3(self):
        return self.my_check(self.my_addr1, self.my_addr3,
                             self.my_string1, self.my_string1)

    # Test (avoid strcmp confusion)
    def init4(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr3 = self._alloc_string(self.my_string3)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr3)

    def check4(self):
        return self.my_check(self.my_addr1, self.my_addr3,
                             self.my_string1, self.my_string3)

    # Properties
    func = "stricmp"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2) & \
        TestSetTest(init3, check3) & TestSetTest(init4, check4)


class TestStrchr(Test):

    # Test
    my_string = "Hello,"
    my_string2 = "He\x00llo,"
    my_char = "l"

    def init1(self):
        self.my_addr = self._alloc_string(self.my_string)

        self._add_arg(0, self.my_addr)
        self._add_arg(1, ord(self.my_char))

    def check1(self):
        result = self._get_result()

        return all([result-self.my_addr == self.my_string.index(self.my_char),
                    self._ensure_mem(self.my_addr, self.my_string.encode('utf-8'))])

    # Test 2
    def init2(self):
        self.my_addr = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr)
        self._add_arg(1, ord(self.my_char))

    def check2(self):
        result = self._get_result()
        return all([result == 0,
                    self._ensure_mem(self.my_addr, self.my_string2.encode('utf-8'))])

    # Properties
    func = "strchr"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2)


class TestStrrchr(Test):

    # Test
    my_string = "Hello, hello, "
    my_string2 = "Hel\x00lo,"
    my_char = "o"

    def init1(self):
        self.my_addr = self._alloc_string(self.my_string)

        self._add_arg(0, self.my_addr)
        self._add_arg(1, ord(self.my_char))

    def check1(self):
        result = self._get_result()
        return all([result-self.my_addr == self.my_string.rindex(self.my_char),
                    self._ensure_mem(self.my_addr, self.my_string.encode('utf-8'))])

    # Test 2
    def init2(self):
        self.my_addr = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr)
        self._add_arg(1, ord(self.my_char))

    def check2(self):
        result = self._get_result()
        return all([result == 0,
                    self._ensure_mem(self.my_addr, self.my_string2.encode('utf-8'))])

    # Properties
    func = "strrchr"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2)


class TestStrnlen(Test):

    # Test1
    my_string = "Hello, w%srld !"
    my_len1 = 4
    my_len2 = 20

    def init1(self):
        self.my_addr = self._alloc_string(self.my_string)
        self._add_arg(0, self.my_addr)
        self._add_arg(1, self.my_len1)

    def check1(self):
        result = self._get_result()

        if result != self.my_len1:
            return False

        return self._ensure_mem(self.my_addr, self.my_string.encode('utf-8') + b"\x00")

    # Test2
    def init2(self):
        self.my_addr = self._alloc_string(self.my_string)
        self._add_arg(0, self.my_addr)
        self._add_arg(1, self.my_len2)

    def check2(self):
        result = self._get_result()

        if result != len(self.my_string):
            return False

        return self._ensure_mem(self.my_addr, self.my_string.encode('utf-8') + b"\x00")

    # Properties
    func = "strnlen"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2)


class TestStrspn(Test):

    def my_check(self, addr1, addr2, str1, str2):
        result = self._get_result()
        length = 0
        for char in str1:
            if char == '\x00':
                break
            if char not in str2:
                break
            length += 1
        return all([result == length,
                    self._ensure_mem(addr1, str1.encode('utf-8')),
                    self._ensure_mem(addr2, str2.encode('utf-8'))])

    # Test
    my_string1 = "Hello,"
    my_string2 = "leH"
    my_string3 = "abcde"

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)

    def check1(self):
        return self.my_check(self.my_addr1, self.my_addr2,
                             self.my_string1, self.my_string2)

    # Test2
    def init2(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr1)

    def check2(self):
        return self.my_check(self.my_addr2, self.my_addr1,
                             self.my_string2, self.my_string1)

    # Test3
    def init3(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr3 = self._alloc_string(self.my_string3)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr3)

    def check3(self):
        return self.my_check(self.my_addr1, self.my_addr3,
                             self.my_string1, self.my_string3)

    # Properties
    func = "strspn"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2) & TestSetTest(init3, check3)


class TestStrpbrk(Test):

    def my_check(self, addr1, addr2, str1, str2, res_found):
        result = self._get_result()
        length = 0
        found = False
        for char in str1:
            if char == '\x00':
                break
            if char in str2:
                found = True
                break
            length += 1
        return all([found == res_found,
                    (found and result - addr1 == length or not found),
                    self._ensure_mem(addr1, str1.encode('utf-8')),
                    self._ensure_mem(addr2, str2.encode('utf-8'))])

    # Test
    my_string1 = "Hello,"
    my_string2 = "elo"
    my_string3 = "abcd"

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)

    def check1(self):
        return self.my_check(self.my_addr1, self.my_addr2,
                             self.my_string1, self.my_string2, True)

    # Test2
    def init2(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr1)

    def check2(self):
        return self.my_check(self.my_addr2, self.my_addr1,
                             self.my_string2, self.my_string1, True)

    # Test3
    def init3(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr3 = self._alloc_string(self.my_string3)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr3)

    def check3(self):
        return self.my_check(self.my_addr1, self.my_addr3,
                             self.my_string1, self.my_string3, False)

    # Properties
    func = "strpbrk"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2) & TestSetTest(init3, check3)


class TestStrtok(Test):

    def reset(self):
        # Do not reset memory
        pass

    # Test
    my_string1 = "Hello, [word]!"
    my_string2 = "[]"
    first_tok = 8

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1, write=True)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)
        self.reset_mem = False

    def check1(self):
        result = self._get_result()
        return all([result == self.my_addr1,
                    self._ensure_mem(self.my_addr1, "Hello, ".encode('utf-8'))])

    # Test2
    def init2(self):
        self._add_arg(0, 0)
        self._add_arg(1, self.my_addr2)

    def check2(self):
        result = self._get_result()
        return all([result == self.my_addr1 + self.first_tok,
                    self._ensure_mem(self.my_addr1, "Hello, \x00word\x00!".encode('utf-8'))])

    # Properties
    func = "strtok"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2)


class TestStrsep(Test):

    def reset(self):
        # Do not reset memory
        pass

    # Test
    my_string1 = "Hello, [word]!"
    my_string2 = "[]"
    first_tok = 8

    def init1(self):

        self.my_addr1 = self._alloc_string(self.my_string1, write=True)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self.my_ptr = self._alloc_pointer(self.my_addr1, write=True)

        self._add_arg(0, self.my_ptr)
        self._add_arg(1, self.my_addr2)
        self.reset_mem = False

    def check1(self):
        result = self._get_result()
        ptr = self._memread_pointer(self.my_ptr)
        return all([result == self.my_addr1,
                    ptr == self.my_addr1 + self.first_tok,
                    self._ensure_mem(self.my_addr1, "Hello, ".encode('utf-8'))])

    # Test2
    def init2(self):
        self._add_arg(0, self.my_ptr)
        self._add_arg(1, self.my_addr2)

    def check2(self):
        result = self._get_result()
        return all([result == self.my_addr1 + self.first_tok,
                    self._ensure_mem(self.my_addr1, "Hello, \x00word\x00!".encode('utf-8'))])

    # Properties
    func = "strsep"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2)


class TestMemset(Test):

    # Test
    my_string1 = "\x11"*0x9
    my_pattern = "A"

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1, write=True)

        # print(f'!!! [string.TestMemset.init1] arg0=0x{self.my_addr1:x}')
        # print(f'!!! [string.TestMemset.init1] arg1={ord(self.my_pattern)}')
        # print(f'!!! [string.TestMemset.init1] arg2={len(self.my_string1)-1}')

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, ord(self.my_pattern))
        self._add_arg(2, len(self.my_string1)-1)

    def check1(self):
        expected_mem = self.my_pattern * (len(self.my_string1) - 1)
        expected_mem += self.my_string1[-1]

        result = self._get_result()

        # print(f'!!! [string.TestMemset.check1] result=0x{result:x}')

        return all([result == self.my_addr1 or
                    result == self.my_addr1 + len(self.my_string1)-1,  # non-standard
                    self._ensure_mem(self.my_addr1, expected_mem.encode('utf-8'))])

    # Properties
    func = "memset"
    tests = TestSetTest(init1, check1)


class TestMemmove(Test):

    # Test
    my_string1 = "toto\x00titi1tututata123456789"
    off = 5
    cpt = 8
    overlap = (my_string1[:off]*3)[:off+cpt] + my_string1[off+cpt:]

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string("\x00"*len(self.my_string1), write=True)

        # print(f'!!! [string.TestMemmove.init1] arg0=0x{self.my_addr2:x}')
        # print(f'!!! [string.TestMemmove.init1] arg1=0x{self.my_addr1:x}')
        # print(f'!!! [string.TestMemmove.init1] arg2={len(self.my_string1)}')

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr1)
        self._add_arg(2, len(self.my_string1))

    def check1(self):
        ignore_retval = True

        retval_cond = True
        if not ignore_retval:
            result = self._get_result()
            retval_cond = result == self.my_addr2

            # print(f'!!! [string.TestMemmove.check1] result=0x{result:x}')

        return all([retval_cond,
                    self._ensure_mem(self.my_addr1, self.my_string1.encode('utf-8')),
                    self._ensure_mem(self.my_addr2, self.my_string1.encode('utf-8')),
                    ])

    # Test 2 (avoid memcpy confusion)

    def init2(self):
        self.my_addr1 = self._alloc_string(self.my_string1, write=True)

        # print(f'!!! [string.TestMemmove.init2] arg0=0x{self.my_addr1+self.off:x}')
        # print(f'!!! [string.TestMemmove.init2] arg1=0x{self.my_addr1:x}')
        # print(f'!!! [string.TestMemmove.init2] arg2={self.cpt}')

        self._add_arg(0, self.my_addr1+self.off)
        self._add_arg(1, self.my_addr1)
        self._add_arg(2, self.cpt)

    def check2(self):
        result = self._get_result()

        # print(f'!!! [string.TestMemmove.check2] result=0x{result:x}')

        return all([result == self.my_addr1+self.off,
                    self._ensure_mem(self.my_addr1+self.off,
                                     self.my_string1[:self.cpt].encode('utf-8'))])

    # Test 3 (avoid memcpy confusion)

    def init3(self):
        self.my_addr1 = self._alloc_string(self.my_string1, write=True)

        # print(f'!!! [string.TestMemmove.init3] arg0=0x{self.my_addr1:x}')
        # print(f'!!! [string.TestMemmove.init3] arg1=0x{self.my_addr1+self.off:x}')
        # print(f'!!! [string.TestMemmove.init3] arg2={self.cpt}')

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr1+self.off)
        self._add_arg(2, self.cpt)

    def check3(self):
        result = self._get_result()

        # print(f'!!! [string.TestMemmove.check3] result=0x{result:x}')

        return all([result == self.my_addr1,
                    self._ensure_mem(self.my_addr1,
                                     self.my_string1[self.off:self.off+self.cpt].encode('utf-8'))])

    # Properties
    func = "memmove"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2) & TestSetTest(init3, check3)


class TestMemmoveWeak(Test):

    # Test
    my_string1 = "NED\x00A1E"
    off = 3
    cpt = 6

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string("\x00"*len(self.my_string1), write=True)

        # print(f'!!! [string.TestMemmoveWeak.init1] arg0=0x{self.my_addr2:x}')
        # print(f'!!! [string.TestMemmoveWeak.init1] arg1=0x{self.my_addr1:x}')
        # print(f'!!! [string.TestMemmoveWeak.init1] arg2={len(self.my_string1)}')

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr1)
        self._add_arg(2, len(self.my_string1))

    def check1(self):
        ignore_retval = True

        retval_cond = True
        if not ignore_retval:
            result = self._get_result()
            retval_cond = result == self.my_addr2

            # print(f'!!! [string.TestMemmoveWeak.check1] result=0x{result:x}')

        return all([retval_cond,
                    self._ensure_mem(self.my_addr1, self.my_string1.encode('utf-8')),
                    self._ensure_mem(self.my_addr2, self.my_string1.encode('utf-8')),
                    ])

    # Test 2 (avoid memcpy confusion)

    def init2(self):
        self.my_addr1 = self._alloc_string(self.my_string1, write=True)

        # print(f'!!! [string.TestMemmoveWeak.init2] arg0=0x{self.my_addr1+self.off:x}')
        # print(f'!!! [string.TestMemmoveWeak.init2] arg1=0x{self.my_addr1:x}')
        # print(f'!!! [string.TestMemmoveWeak.init2] arg2={self.cpt}')

        self._add_arg(0, self.my_addr1+self.off)
        self._add_arg(1, self.my_addr1)
        self._add_arg(2, self.cpt)

    def check2(self):
        result = self._get_result()

        # print(f'!!! [string.TestMemmoveWeak.check2] result=0x{result:x}')

        return all([result == self.my_addr1+self.off,
                    self._ensure_mem(self.my_addr1+self.off,
                                     self.my_string1[:self.cpt].encode('utf-8'))])

    # Test 3 (avoid memcpy confusion)

    def init3(self):
        self.my_addr1 = self._alloc_string(self.my_string1, write=True)

        # print(f'!!! [string.TestMemmoveWeak.init3] arg0=0x{self.my_addr1:x}')
        # print(f'!!! [string.TestMemmoveWeak.init3] arg1=0x{self.my_addr1+self.off:x}')
        # print(f'!!! [string.TestMemmoveWeak.init3] arg2={self.cpt}')

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr1+self.off)
        self._add_arg(2, self.cpt)

    def check3(self):
        result = self._get_result()

        # print(f'!!! [string.TestMemmoveWeak.check3] result=0x{result:x}')

        return all([result == self.my_addr1,
                    self._ensure_mem(self.my_addr1,
                                     self.my_string1[self.off:self.off+self.cpt].encode('utf-8'))])

    # Properties
    func = "memmove"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2) & TestSetTest(init3, check3)


class TestMemcpy(TestMemmove):

    my_string2 = "AbCdEfG"

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string2)
        self.my_addr2 = self._alloc_string("\x00"*len(self.my_string2), write=True)

        # print(f'!!! [string.TestMemcpy.init1] arg0=0x{self.my_addr2:x}')
        # print(f'!!! [string.TestMemcpy.init1] arg1=0x{self.my_addr1:x}')
        # print(f'!!! [string.TestMemcpy.init1] arg2={len(self.my_string2)}')

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr1)
        self._add_arg(2, len(self.my_string2))

    def check1(self):
        ignore_retval = True

        retval_cond = True
        if not ignore_retval:
            result = self._get_result()
            retval_cond = result == self.my_addr2

            # print(f'!!! [string.TestMemcpy.check1] result=0x{result:x}')

        return all([retval_cond,
                    self._ensure_mem(self.my_addr1, self.my_string2.encode('utf-8')),
                    self._ensure_mem(self.my_addr2, self.my_string2.encode('utf-8')),
                    ])

    def check2(self):
        ignore_retval = True

        retval_cond = True
        if not ignore_retval:
            result = self._get_result()
            retval_cond = result == self.my_addr1+self.off

            # print(f'!!! [string.TestMemcpy.check2] result=0x{result:x}')

        return all([retval_cond,
                    not self._ensure_mem(self.my_addr1+self.off,
                                         self.my_string1[:self.cpt].encode('utf-8'))])

    def check3(self):
        ignore_retval = True

        retval_cond = True
        if not ignore_retval:
            result = self._get_result()
            retval_cond = result == self.my_addr1

            # print(f'!!! [string.TestMemcpy.check3] result=0x{result:x}')

        return all([retval_cond,
                    not self._ensure_mem(self.my_addr1,
                                         self.my_string1[self.off:self.off+self.cpt]
                                         .encode('utf-8'))])

    # Properties
    func = "memcpy"
    # At least one of the test2/test3 may fail for memcpy
    tests = (TestSetTest(TestMemmove.init1, TestMemmove.check1) &
             (TestSetTest(TestMemmove.init2, check2) | TestSetTest(TestMemmove.init3, check3))
             )


class TestMemcpyWeak(TestMemmoveWeak):

    def check2(self):
        ignore_retval = True

        retval_cond = True
        if not ignore_retval:
            result = self._get_result()
            retval_cond = result == self.my_addr1+self.off

            # print(f'!!! [string.TestMemcpyWeak.check2] result=0x{result:x}')

        return all([retval_cond,
                    not self._ensure_mem(self.my_addr1+self.off,
                                         self.my_string1[:self.cpt].encode('utf-8'))])

    def check3(self):
        ignore_retval = True

        retval_cond = True
        if not ignore_retval:
            result = self._get_result()
            retval_cond = result == self.my_addr1

            # print(f'!!! [string.TestMemcpyWeak.check3] result=0x{result:x}')

        return all([retval_cond,
                    not self._ensure_mem(self.my_addr1,
                                         self.my_string1[self.off:self.off+self.cpt]
                                         .encode('utf-8'))])

    # Properties
    func = "memcpy"
    # At least one of the test2/test3 may fail for memcpy
    tests = (
        TestSetTest(TestMemmoveWeak.init1, TestMemmoveWeak.check1) &
        (TestSetTest(TestMemmoveWeak.init2, check2) | TestSetTest(TestMemmoveWeak.init3, check3))
    )


class TestStrrev(Test):

    # Test1
    my_string = "Hello, w%srld !"

    def init(self):
        self.my_addr = self._alloc_string(self.my_string, write=True)
        self._add_arg(0, self.my_addr)

    def check(self):
        result = self._get_result()

        if result != self.my_addr:
            return False
        return self._ensure_mem(self.my_addr, self.my_string[::-1].encode('utf-8') + b"\x00")

    # Properties
    func = "strrev"
    tests = TestSetTest(init, check)


class TestMemcmp(Test):

    def my_check(self, addr1, addr2, str1, str2):
        result = self._get_result()
        result = self._to_int(result)
        if result < 0:
            result = -1
        elif result > 0:
            result = 1

        return all([result == cmp(str1, str2),
                    self._ensure_mem(addr1, str1.encode('utf-8')),
                    self._ensure_mem(addr2, str2.encode('utf-8'))])

    # Test
    my_string1 = "He\x00l2lo"
    my_string2 = "He\x00l1lo"
    my_len = len(my_string1)

    def init1(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr2)
        self._add_arg(2, self.my_len)

    def check1(self):
        return self.my_check(self.my_addr1, self.my_addr2,
                             self.my_string1, self.my_string2)

    # Test2
    def init2(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr2 = self._alloc_string(self.my_string2)

        self._add_arg(0, self.my_addr2)
        self._add_arg(1, self.my_addr1)
        self._add_arg(2, self.my_len)

    def check2(self):
        return self.my_check(self.my_addr2, self.my_addr1,
                             self.my_string2, self.my_string1)

    # Test3
    def init3(self):
        self.my_addr1 = self._alloc_string(self.my_string1)
        self.my_addr3 = self._alloc_string(self.my_string1)

        self._add_arg(0, self.my_addr1)
        self._add_arg(1, self.my_addr3)
        self._add_arg(2, self.my_len)

    def check3(self):
        return self.my_check(self.my_addr1, self.my_addr3,
                             self.my_string1, self.my_string1)

    # Properties
    func = "memcmp"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2) & TestSetTest(init3, check3)


class TestBzero(Test):

    # Test1
    my_string = "Hello \x00, w%srld !, hello world"
    my_len = len(my_string)

    def init1(self):
        self.my_addr = self._alloc_string(self.my_string, write=True)
        self._add_arg(0, self.my_addr)
        self._add_arg(1, self.my_len)

    def check1(self):
        return self._ensure_mem(self.my_addr, self.my_len * b"\x00")

    # Test2
    my_string2 = my_string * 50
    my_len2 = len(my_string2)

    def init2(self):
        self.my_addr = self._alloc_string(self.my_string2, write=True)
        self._add_arg(0, self.my_addr)
        self._add_arg(1, self.my_len2)

    def check2(self):
        return self._ensure_mem(self.my_addr, self.my_len2 * b"\x00")

    # Properties
    func = "bzero"
    tests = TestSetTest(init1, check1) & TestSetTest(init2, check2)


TESTS = [TestStrlen, TestStrnicmp, TestStrcpy, TestStrncpy,
         TestStrcat, TestStrncat, TestStrcmp, TestStrchr,
         TestStrrchr, TestStrnlen, TestStrspn, TestStrpbrk,
         TestStrtok, TestStrsep, TestMemset,
         # TestMemmove, TestMemcpy,
         TestMemmoveWeak, TestMemcpyWeak,
         TestStricmp, TestStrrev, TestMemcmp, TestBzero,
         TestStrncmp]

# TESTS = [TestMemset, TestMemmove, TestMemcpy]
