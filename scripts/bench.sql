DROP TABLE bench;

CREATE TABLE bench (
	mark VARCHAR(30) NOT NULL,
	time BIGINT NOT NULL,
	timeuser BIGINT NOT NULL,
	compilation ENUM('byte','opt') NOT NULL,
	test VARCHAR(100) NOT NULL,
	result ENUM('ok','fail') NOT NULL,
	options SET('gc-off','gc-on')
);

DESCRIBE bench; 
