# Copyright 2013-2015 Eric Schkufza, Rahul Sharma, Berkeley Churchill, Stefan Heule
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

all: orig extract testcases search replace

orig:
	g++ -std=c++11 -fno-inline -O3 main.cc

time:
	time --quiet ./a.out 1000000000

extract:
	stoke extract --config extract.conf

testcases:
	stoke testcase --target bins/_Z6paritym.s > parity.tc

search:
	stoke search --config search.conf

replace:
	stoke replace --config replace.conf

clean:
	rm -rf bins ./a.out *.tc *.s
