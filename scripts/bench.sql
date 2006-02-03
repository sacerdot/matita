DROP TABLE bench;

CREATE TABLE bench (
	mark VARCHAR(100) NOT NULL,
	time VARCHAR(8) NOT NULL,
	timeuser VARCHAR(8) NOT NULL,
	compilation ENUM('byte','opt') NOT NULL,
	test VARCHAR(100) NOT NULL,
	result ENUM('ok','fail') NOT NULL,
	options SET('gc-off','gc-on')
);

DESCRIBE bench; 
