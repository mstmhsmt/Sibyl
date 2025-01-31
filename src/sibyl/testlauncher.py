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

"""This module provides a way to prepare and launch Sibyl tests on a binary"""


import time
# import signal
# import logging
from miasm.analysis.binary import Container, ContainerPE, ContainerELF
from miasm.core.locationdb import LocationDB

from sibyl.commons import init_logger, END_ADDR  # , TimeoutException
from sibyl.engine import QEMUEngine, MiasmEngine
from sibyl.config import config


class TestLauncher(object):
    "Launch tests for a function and report matching candidates"

    def __init__(self, filename_or_content, machine, abicls, tests_cls, engine_name,
                 map_addr=0, early_quit_all=True):

        # quit all tests when a timeout occurred
        self.early_quit_all = early_quit_all

        # Logging facilities
        self.logger = init_logger("testlauncher")

        # Prepare JiT engine
        self.machine = machine
        self.init_engine(engine_name)

        # Init and snapshot VM
        if isinstance(filename_or_content, str):
            self.load_vm(filename_or_content, map_addr)
        elif isinstance(filename_or_content, bytes):
            self.load_vm_bytes(filename_or_content, map_addr)
        else:
            raise TypeError('The first arg should be str or bytes')

        self.init_stub()
        self.snapshot = self.engine.take_snapshot()

        # Init tests
        self.init_abi(abicls)
        self.initialize_tests(tests_cls)

    def init_stub(self):
        """Initialize stubbing capabilities"""
        if not isinstance(self.engine, MiasmEngine):
            # Unsupported capability
            return

        # Get stubs' implementation
        context = {}
        for fpath in config.stubs:
            exec(compile(open(fpath, "rb").read(), fpath, 'exec'), context)
        if not context:
            return

        libs = None
        if isinstance(self.ctr, ContainerPE):
            from miasm.jitter.loader.pe import preload_pe, libimp_pe
            libs = libimp_pe()
            preload_pe(self.jitter.vm, self.ctr.executable, libs)

        elif isinstance(self.ctr, ContainerELF):
            from miasm.jitter.loader.elf import preload_elf, libimp_elf
            libs = libimp_elf()
            preload_elf(self.jitter.vm, self.ctr.executable, libs)

        else:
            return

        # Add associated breakpoints
        self.jitter.add_lib_handler(libs, context)

    def initialize_tests(self, tests_cls):
        tests = []
        for testcls in tests_cls:
            tests.append(testcls(self.jitter, self.abi))
        self.tests = tests

    def load_vm(self, filename, map_addr):
        self.ctr = Container.from_stream(open(filename, 'rb'), LocationDB(), vm=self.jitter.vm,
                                         addr=map_addr)
        self.jitter.cpu.init_regs()
        self.jitter.init_stack()

    def load_vm_bytes(self, bs, map_addr):
        self.ctr = Container.from_string(bs, LocationDB(), vm=self.jitter.vm, addr=map_addr)
        self.jitter.cpu.init_regs()
        self.jitter.init_stack()

    def init_engine(self, engine_name):
        if engine_name == "qemu":
            self.engine = QEMUEngine(self.machine)
        else:
            self.engine = MiasmEngine(self.machine, engine_name)
        self.jitter = self.engine.jitter

    def init_abi(self, abicls):
        ira = self.machine.lifter_model_call(LocationDB())
        self.abi = abicls(self.jitter, ira)

    def launch_tests(self, test, address, timeout_seconds=0):
        # Variables to remind between two "launch_test"
        self._temp_reset_mem = True

        # Reset between functions
        test.reset_full()

        # Callback to launch
        def launch_test(init, check):
            """Launch a test associated with @init, @check"""

            # Reset state
            self.engine.restore_snapshot(memory=self._temp_reset_mem)
            self.abi.reset()
            test.reset()

            # Prepare VM
            init(test)
            self.abi.prepare_call(ret_addr=END_ADDR)

            # Run code
            start_time = time.monotonic()
            status = self.engine.run(address, timeout_seconds)
            lap_time = time.monotonic() - start_time

            self.timeout_flag = lap_time > timeout_seconds

            if not status:
                # Early quit
                self._temp_reset_mem = True
                return False

            # Check result
            to_ret = check(test)

            # Update flags
            self._temp_reset_mem = test.reset_mem

            return to_ret

        # Launch subtests
        status = test.tests.execute(launch_test)
        if status:
            self._possible_funcs.append(test.func)

    def run(self, address, *args, **kwargs):
        self._possible_funcs = []

        nb_tests = len(self.tests)
        self.logger.info("Launch tests (%d available functions)" % (nb_tests))
        starttime = time.time()

        self.engine.prepare_run()

        for test in self.tests:
            # print('!!! [testlauncher.run] {test}')
            self.launch_tests(test, address, *args, **kwargs)
            if self.early_quit_all and self.timeout_flag:
                break

        self.logger.info("Total time: %.4f seconds" % (time.time() - starttime))
        return self._possible_funcs

    def get_possible_funcs(self):
        return self._possible_funcs
    possible_funcs = property(get_possible_funcs)
