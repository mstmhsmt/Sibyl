# This file is part of Sibyl.
# Copyright 2017 Camille MOUGEY <camille.mougey@cea.fr>
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

FROM miasm/tested:latest
MAINTAINER Camille Mougey <camille.mougey@cea.fr>
USER root

# Get unicorn
RUN pip3 install --pre unicorn

# Get Sibyl
ADD https://github.com/mstmhsmt/Sibyl/archive/aies0.tar.gz /opt/Sibyl.tar.gz
RUN cd /opt &&\
    tar xzvf Sibyl.tar.gz &&\
    rm Sibyl.tar.gz &&\
    mv Sibyl-aies0 Sibyl &&\
    chown -Rh miasm Sibyl &&\
    cd Sibyl &&\
    python3 setup.py install

# Prepare the environment
WORKDIR /opt/Sibyl
USER miasm

CMD ["/usr/local/bin/sibyl"]
