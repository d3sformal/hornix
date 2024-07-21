#include <iostream>
#include <stdexcept>
#include <fstream>
#include <string>

int main(int argc, char *argv[]){
	if (argc != 3) {
		std::invalid_argument("Wrong number of arguments. Filename and result needed.");
	}

	auto filename = std::string(argv[1]);
	auto result = std::string(argv[2]);

	std::string name = filename.append(".yml");

	std::ifstream myfile(name);
	std::string myline;
	std::string expected_result = "aaa";
	
	while (myfile) {
		std::getline(myfile, myline); 
		if (myline.find("property_file: ../properties/unreach-call.prp") != std::string::npos) {
			std::getline(myfile, myline);
			if (myline.find("expected_verdict: false") != std::string::npos) {
				expected_result = "unsat";
			}
			else {
				expected_result = "sat";
			}
			break;
		}
	}

	if (expected_result.compare(result))
	{
		std::cout << "GOOD RESULT";
	}
	else {
		std::cout << "BAD RESULT";
	}

	return 0;
}